%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:29 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 158 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 302 expanded)
%              Number of equality atoms :   37 (  78 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_46,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_84,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_95,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_91])).

tff(c_30,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = k1_xboole_0
      | k2_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_30])).

tff(c_100,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_101,plain,(
    ! [A_58] :
      ( k2_relat_1(A_58) = k1_xboole_0
      | k1_relat_1(A_58) != k1_xboole_0
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_108,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_101])).

tff(c_110,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_108])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_111,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_120,plain,(
    v4_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_121,plain,(
    ! [B_62,A_63] :
      ( k7_relat_1(B_62,A_63) = B_62
      | ~ v4_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,
    ( k7_relat_1('#skF_6','#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_120,c_121])).

tff(c_127,plain,(
    k7_relat_1('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_124])).

tff(c_151,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(k1_relat_1(B_68),A_69) = k1_relat_1(k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_306,plain,(
    ! [D_88,A_89,B_90] :
      ( r2_hidden(D_88,A_89)
      | ~ r2_hidden(D_88,k1_relat_1(k7_relat_1(B_90,A_89)))
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_4])).

tff(c_317,plain,(
    ! [D_88] :
      ( r2_hidden(D_88,'#skF_5')
      | ~ r2_hidden(D_88,k1_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_306])).

tff(c_327,plain,(
    ! [D_91] :
      ( r2_hidden(D_91,'#skF_5')
      | ~ r2_hidden(D_91,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_317])).

tff(c_339,plain,
    ( r2_hidden('#skF_3'(k1_relat_1('#skF_6')),'#skF_5')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_327])).

tff(c_344,plain,(
    r2_hidden('#skF_3'(k1_relat_1('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_339])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_354,plain,(
    m1_subset_1('#skF_3'(k1_relat_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_344,c_22])).

tff(c_414,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_433,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_414])).

tff(c_67,plain,(
    ! [D_51] :
      ( ~ r2_hidden(D_51,k1_relset_1('#skF_5','#skF_4','#skF_6'))
      | ~ m1_subset_1(D_51,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_3'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5')
    | k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_67])).

tff(c_221,plain,(
    ~ m1_subset_1('#skF_3'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_437,plain,(
    ~ m1_subset_1('#skF_3'(k1_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_221])).

tff(c_441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_437])).

tff(c_442,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_724,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_739,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_724])).

tff(c_744,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_739])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_744])).

tff(c_748,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_1196,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1211,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_1196])).

tff(c_1216,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_1211])).

tff(c_1218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:15:54 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.46  
% 3.07/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.10/1.46  
% 3.10/1.46  %Foreground sorts:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Background operators:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Foreground operators:
% 3.10/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.10/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.10/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.10/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.10/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.46  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.46  
% 3.10/1.48  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.10/1.48  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.10/1.48  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.10/1.48  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.10/1.48  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.10/1.48  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.48  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.10/1.48  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.10/1.48  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.10/1.48  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.10/1.48  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.10/1.48  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.48  tff(c_46, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.10/1.48  tff(c_26, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.10/1.48  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.10/1.48  tff(c_84, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.10/1.48  tff(c_91, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_84])).
% 3.10/1.48  tff(c_95, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_91])).
% 3.10/1.48  tff(c_30, plain, (![A_18]: (k1_relat_1(A_18)=k1_xboole_0 | k2_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.48  tff(c_99, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_30])).
% 3.10/1.48  tff(c_100, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 3.10/1.48  tff(c_101, plain, (![A_58]: (k2_relat_1(A_58)=k1_xboole_0 | k1_relat_1(A_58)!=k1_xboole_0 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.48  tff(c_108, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_101])).
% 3.10/1.48  tff(c_110, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_100, c_108])).
% 3.10/1.48  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.48  tff(c_111, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.10/1.48  tff(c_120, plain, (v4_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_111])).
% 3.10/1.48  tff(c_121, plain, (![B_62, A_63]: (k7_relat_1(B_62, A_63)=B_62 | ~v4_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.48  tff(c_124, plain, (k7_relat_1('#skF_6', '#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_120, c_121])).
% 3.10/1.48  tff(c_127, plain, (k7_relat_1('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_124])).
% 3.10/1.48  tff(c_151, plain, (![B_68, A_69]: (k3_xboole_0(k1_relat_1(B_68), A_69)=k1_relat_1(k7_relat_1(B_68, A_69)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.48  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.48  tff(c_306, plain, (![D_88, A_89, B_90]: (r2_hidden(D_88, A_89) | ~r2_hidden(D_88, k1_relat_1(k7_relat_1(B_90, A_89))) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_151, c_4])).
% 3.10/1.48  tff(c_317, plain, (![D_88]: (r2_hidden(D_88, '#skF_5') | ~r2_hidden(D_88, k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_306])).
% 3.10/1.48  tff(c_327, plain, (![D_91]: (r2_hidden(D_91, '#skF_5') | ~r2_hidden(D_91, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_317])).
% 3.10/1.48  tff(c_339, plain, (r2_hidden('#skF_3'(k1_relat_1('#skF_6')), '#skF_5') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_327])).
% 3.10/1.48  tff(c_344, plain, (r2_hidden('#skF_3'(k1_relat_1('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_110, c_339])).
% 3.10/1.48  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.10/1.48  tff(c_354, plain, (m1_subset_1('#skF_3'(k1_relat_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_344, c_22])).
% 3.10/1.48  tff(c_414, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.48  tff(c_433, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_414])).
% 3.10/1.48  tff(c_67, plain, (![D_51]: (~r2_hidden(D_51, k1_relset_1('#skF_5', '#skF_4', '#skF_6')) | ~m1_subset_1(D_51, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.10/1.48  tff(c_72, plain, (~m1_subset_1('#skF_3'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5') | k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_67])).
% 3.10/1.48  tff(c_221, plain, (~m1_subset_1('#skF_3'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 3.10/1.48  tff(c_437, plain, (~m1_subset_1('#skF_3'(k1_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_221])).
% 3.10/1.48  tff(c_441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_354, c_437])).
% 3.10/1.48  tff(c_442, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 3.10/1.48  tff(c_724, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.48  tff(c_739, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_724])).
% 3.10/1.48  tff(c_744, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_442, c_739])).
% 3.10/1.48  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_744])).
% 3.10/1.48  tff(c_748, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 3.10/1.48  tff(c_1196, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.48  tff(c_1211, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_1196])).
% 3.10/1.48  tff(c_1216, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_748, c_1211])).
% 3.10/1.48  tff(c_1218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1216])).
% 3.10/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  Inference rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Ref     : 0
% 3.10/1.48  #Sup     : 261
% 3.10/1.48  #Fact    : 0
% 3.10/1.48  #Define  : 0
% 3.10/1.48  #Split   : 3
% 3.10/1.48  #Chain   : 0
% 3.10/1.48  #Close   : 0
% 3.10/1.48  
% 3.10/1.48  Ordering : KBO
% 3.10/1.48  
% 3.10/1.48  Simplification rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Subsume      : 12
% 3.10/1.48  #Demod        : 91
% 3.10/1.48  #Tautology    : 110
% 3.10/1.48  #SimpNegUnit  : 6
% 3.10/1.48  #BackRed      : 12
% 3.10/1.48  
% 3.10/1.48  #Partial instantiations: 0
% 3.10/1.48  #Strategies tried      : 1
% 3.10/1.48  
% 3.10/1.48  Timing (in seconds)
% 3.10/1.48  ----------------------
% 3.10/1.48  Preprocessing        : 0.32
% 3.10/1.48  Parsing              : 0.17
% 3.10/1.48  CNF conversion       : 0.02
% 3.10/1.48  Main loop            : 0.41
% 3.10/1.48  Inferencing          : 0.15
% 3.10/1.48  Reduction            : 0.12
% 3.10/1.48  Demodulation         : 0.08
% 3.10/1.48  BG Simplification    : 0.02
% 3.10/1.48  Subsumption          : 0.07
% 3.10/1.48  Abstraction          : 0.02
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.76
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
