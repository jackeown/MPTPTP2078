%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:33 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 173 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 393 expanded)
%              Number of equality atoms :   31 ( 100 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_95,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_99,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_95])).

tff(c_106,plain,(
    ! [A_82,B_83,C_84] :
      ( m1_subset_1(k2_relset_1(A_82,B_83,C_84),k1_zfmisc_1(B_83))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_106])).

tff(c_128,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_122])).

tff(c_4,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_137,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_86,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_86])).

tff(c_183,plain,(
    ! [B_101,A_102,C_103] :
      ( k1_xboole_0 = B_101
      | k1_relset_1(A_102,B_101,C_103) = A_102
      | ~ v1_funct_2(C_103,A_102,B_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_183])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_90,c_190])).

tff(c_195,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_10,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,
    ( k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_10])).

tff(c_204,plain,(
    k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_200])).

tff(c_254,plain,(
    ! [A_115,B_116,D_117] :
      ( k1_funct_1(A_115,'#skF_4'(A_115,B_116,k9_relat_1(A_115,B_116),D_117)) = D_117
      | ~ r2_hidden(D_117,k9_relat_1(A_115,B_116))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_224,plain,(
    ! [A_108,B_109,D_110] :
      ( r2_hidden('#skF_4'(A_108,B_109,k9_relat_1(A_108,B_109),D_110),B_109)
      | ~ r2_hidden(D_110,k9_relat_1(A_108,B_109))
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ! [E_65] :
      ( k1_funct_1('#skF_8',E_65) != '#skF_7'
      | ~ r2_hidden(E_65,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_239,plain,(
    ! [A_108,D_110] :
      ( k1_funct_1('#skF_8','#skF_4'(A_108,'#skF_5',k9_relat_1(A_108,'#skF_5'),D_110)) != '#skF_7'
      | ~ r2_hidden(D_110,k9_relat_1(A_108,'#skF_5'))
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_224,c_54])).

tff(c_261,plain,(
    ! [D_117] :
      ( D_117 != '#skF_7'
      | ~ r2_hidden(D_117,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_117,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_239])).

tff(c_286,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_62,c_204,c_71,c_62,c_204,c_261])).

tff(c_56,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_100,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_56])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_100])).

tff(c_289,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_301,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_2])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_301])).

tff(c_304,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.29  
% 2.25/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.25/1.29  
% 2.25/1.29  %Foreground sorts:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Background operators:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Foreground operators:
% 2.25/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.25/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.25/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.25/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.25/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.25/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.25/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.25/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.29  
% 2.25/1.31  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.25/1.31  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.25/1.31  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.25/1.31  tff(f_33, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.25/1.31  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.25/1.31  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.25/1.31  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.25/1.31  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.25/1.31  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.25/1.31  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.62/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.62/1.31  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.62/1.31  tff(c_95, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.62/1.31  tff(c_99, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_95])).
% 2.62/1.31  tff(c_106, plain, (![A_82, B_83, C_84]: (m1_subset_1(k2_relset_1(A_82, B_83, C_84), k1_zfmisc_1(B_83)) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.31  tff(c_122, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_99, c_106])).
% 2.62/1.31  tff(c_128, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_122])).
% 2.62/1.31  tff(c_4, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.31  tff(c_134, plain, (![A_1]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_1, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_128, c_4])).
% 2.62/1.31  tff(c_137, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_134])).
% 2.62/1.31  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.31  tff(c_65, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.31  tff(c_68, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_65])).
% 2.62/1.31  tff(c_71, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_68])).
% 2.62/1.31  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.62/1.31  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.62/1.31  tff(c_86, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.62/1.31  tff(c_90, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_86])).
% 2.62/1.31  tff(c_183, plain, (![B_101, A_102, C_103]: (k1_xboole_0=B_101 | k1_relset_1(A_102, B_101, C_103)=A_102 | ~v1_funct_2(C_103, A_102, B_101) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.31  tff(c_190, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_183])).
% 2.62/1.31  tff(c_194, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_90, c_190])).
% 2.62/1.31  tff(c_195, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_194])).
% 2.62/1.31  tff(c_10, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.31  tff(c_200, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_195, c_10])).
% 2.62/1.31  tff(c_204, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_200])).
% 2.62/1.31  tff(c_254, plain, (![A_115, B_116, D_117]: (k1_funct_1(A_115, '#skF_4'(A_115, B_116, k9_relat_1(A_115, B_116), D_117))=D_117 | ~r2_hidden(D_117, k9_relat_1(A_115, B_116)) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.31  tff(c_224, plain, (![A_108, B_109, D_110]: (r2_hidden('#skF_4'(A_108, B_109, k9_relat_1(A_108, B_109), D_110), B_109) | ~r2_hidden(D_110, k9_relat_1(A_108, B_109)) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.31  tff(c_54, plain, (![E_65]: (k1_funct_1('#skF_8', E_65)!='#skF_7' | ~r2_hidden(E_65, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.62/1.31  tff(c_239, plain, (![A_108, D_110]: (k1_funct_1('#skF_8', '#skF_4'(A_108, '#skF_5', k9_relat_1(A_108, '#skF_5'), D_110))!='#skF_7' | ~r2_hidden(D_110, k9_relat_1(A_108, '#skF_5')) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_224, c_54])).
% 2.62/1.31  tff(c_261, plain, (![D_117]: (D_117!='#skF_7' | ~r2_hidden(D_117, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_117, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_254, c_239])).
% 2.62/1.31  tff(c_286, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_62, c_204, c_71, c_62, c_204, c_261])).
% 2.62/1.31  tff(c_56, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.62/1.31  tff(c_100, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_56])).
% 2.62/1.31  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_100])).
% 2.62/1.31  tff(c_289, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_194])).
% 2.62/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.62/1.31  tff(c_301, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_2])).
% 2.62/1.31  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_301])).
% 2.62/1.31  tff(c_304, plain, (![A_1]: (~r2_hidden(A_1, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_134])).
% 2.62/1.31  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_100])).
% 2.62/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.31  
% 2.62/1.31  Inference rules
% 2.62/1.31  ----------------------
% 2.62/1.31  #Ref     : 0
% 2.62/1.31  #Sup     : 50
% 2.62/1.31  #Fact    : 0
% 2.62/1.31  #Define  : 0
% 2.62/1.31  #Split   : 4
% 2.62/1.31  #Chain   : 0
% 2.62/1.31  #Close   : 0
% 2.62/1.31  
% 2.62/1.31  Ordering : KBO
% 2.62/1.31  
% 2.62/1.31  Simplification rules
% 2.62/1.31  ----------------------
% 2.62/1.31  #Subsume      : 3
% 2.62/1.31  #Demod        : 51
% 2.62/1.31  #Tautology    : 15
% 2.62/1.31  #SimpNegUnit  : 3
% 2.62/1.31  #BackRed      : 11
% 2.62/1.31  
% 2.62/1.31  #Partial instantiations: 0
% 2.62/1.31  #Strategies tried      : 1
% 2.62/1.31  
% 2.62/1.31  Timing (in seconds)
% 2.62/1.31  ----------------------
% 2.62/1.31  Preprocessing        : 0.33
% 2.62/1.31  Parsing              : 0.17
% 2.62/1.31  CNF conversion       : 0.03
% 2.62/1.31  Main loop            : 0.22
% 2.62/1.31  Inferencing          : 0.07
% 2.62/1.31  Reduction            : 0.07
% 2.62/1.31  Demodulation         : 0.05
% 2.62/1.31  BG Simplification    : 0.02
% 2.62/1.31  Subsumption          : 0.04
% 2.62/1.31  Abstraction          : 0.02
% 2.62/1.31  MUC search           : 0.00
% 2.62/1.31  Cooper               : 0.00
% 2.62/1.31  Total                : 0.58
% 2.62/1.31  Index Insertion      : 0.00
% 2.62/1.31  Index Deletion       : 0.00
% 2.62/1.31  Index Matching       : 0.00
% 2.62/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
