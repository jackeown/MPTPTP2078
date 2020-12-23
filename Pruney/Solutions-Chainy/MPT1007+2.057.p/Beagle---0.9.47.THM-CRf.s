%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:18 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   70 (  82 expanded)
%              Number of leaves         :   39 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 136 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_208,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_212,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_208])).

tff(c_335,plain,(
    ! [B_143,A_144,C_145] :
      ( k1_xboole_0 = B_143
      | k1_relset_1(A_144,B_143,C_145) = A_144
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_342,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_335])).

tff(c_346,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_212,c_342])).

tff(c_347,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_346])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(A_59,C_60)
      | ~ r1_tarski(k2_tarski(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [A_65,B_66] : r2_hidden(A_65,k2_tarski(A_65,B_66)) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_98,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_369,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_98])).

tff(c_90,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_90])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_217,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_221,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_217])).

tff(c_233,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1(k2_relset_1(A_111,B_112,C_113),k1_zfmisc_1(B_112))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_248,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_233])).

tff(c_253,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_248])).

tff(c_263,plain,(
    ! [B_119,A_120] :
      ( r2_hidden(k1_funct_1(B_119,A_120),k2_relat_1(B_119))
      | ~ r2_hidden(A_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [C_37,A_34,B_35] :
      ( r2_hidden(C_37,A_34)
      | ~ r2_hidden(C_37,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_437,plain,(
    ! [B_155,A_156,A_157] :
      ( r2_hidden(k1_funct_1(B_155,A_156),A_157)
      | ~ m1_subset_1(k2_relat_1(B_155),k1_zfmisc_1(A_157))
      | ~ r2_hidden(A_156,k1_relat_1(B_155))
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_263,c_28])).

tff(c_439,plain,(
    ! [A_156] :
      ( r2_hidden(k1_funct_1('#skF_3',A_156),'#skF_2')
      | ~ r2_hidden(A_156,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_253,c_437])).

tff(c_443,plain,(
    ! [A_158] :
      ( r2_hidden(k1_funct_1('#skF_3',A_158),'#skF_2')
      | ~ r2_hidden(A_158,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60,c_439])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_448,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_443,c_52])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:46:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.40  
% 2.46/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.46/1.40  
% 2.46/1.40  %Foreground sorts:
% 2.46/1.40  
% 2.46/1.40  
% 2.46/1.40  %Background operators:
% 2.46/1.40  
% 2.46/1.40  
% 2.46/1.40  %Foreground operators:
% 2.46/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.46/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.46/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.46/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.40  
% 2.46/1.41  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.46/1.41  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.41  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.46/1.41  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.46/1.41  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.46/1.41  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.41  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.46/1.41  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.46/1.41  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.46/1.41  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.46/1.41  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.46/1.41  tff(c_58, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.46/1.41  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.46/1.41  tff(c_208, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.41  tff(c_212, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_208])).
% 2.46/1.41  tff(c_335, plain, (![B_143, A_144, C_145]: (k1_xboole_0=B_143 | k1_relset_1(A_144, B_143, C_145)=A_144 | ~v1_funct_2(C_145, A_144, B_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.46/1.41  tff(c_342, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_335])).
% 2.46/1.41  tff(c_346, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_212, c_342])).
% 2.46/1.41  tff(c_347, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_346])).
% 2.46/1.41  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.41  tff(c_81, plain, (![A_59, C_60, B_61]: (r2_hidden(A_59, C_60) | ~r1_tarski(k2_tarski(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.41  tff(c_95, plain, (![A_65, B_66]: (r2_hidden(A_65, k2_tarski(A_65, B_66)))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.46/1.41  tff(c_98, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_95])).
% 2.46/1.41  tff(c_369, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_347, c_98])).
% 2.46/1.41  tff(c_90, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.46/1.41  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_90])).
% 2.46/1.41  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.46/1.41  tff(c_217, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.46/1.41  tff(c_221, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_217])).
% 2.46/1.41  tff(c_233, plain, (![A_111, B_112, C_113]: (m1_subset_1(k2_relset_1(A_111, B_112, C_113), k1_zfmisc_1(B_112)) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.41  tff(c_248, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_221, c_233])).
% 2.46/1.41  tff(c_253, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_248])).
% 2.46/1.41  tff(c_263, plain, (![B_119, A_120]: (r2_hidden(k1_funct_1(B_119, A_120), k2_relat_1(B_119)) | ~r2_hidden(A_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.41  tff(c_28, plain, (![C_37, A_34, B_35]: (r2_hidden(C_37, A_34) | ~r2_hidden(C_37, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.46/1.41  tff(c_437, plain, (![B_155, A_156, A_157]: (r2_hidden(k1_funct_1(B_155, A_156), A_157) | ~m1_subset_1(k2_relat_1(B_155), k1_zfmisc_1(A_157)) | ~r2_hidden(A_156, k1_relat_1(B_155)) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_263, c_28])).
% 2.46/1.41  tff(c_439, plain, (![A_156]: (r2_hidden(k1_funct_1('#skF_3', A_156), '#skF_2') | ~r2_hidden(A_156, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_253, c_437])).
% 2.46/1.41  tff(c_443, plain, (![A_158]: (r2_hidden(k1_funct_1('#skF_3', A_158), '#skF_2') | ~r2_hidden(A_158, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60, c_439])).
% 2.46/1.41  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.46/1.41  tff(c_448, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_443, c_52])).
% 2.46/1.41  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_448])).
% 2.46/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.41  
% 2.46/1.41  Inference rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Ref     : 0
% 2.46/1.41  #Sup     : 84
% 2.46/1.41  #Fact    : 0
% 2.46/1.41  #Define  : 0
% 2.46/1.41  #Split   : 0
% 2.46/1.41  #Chain   : 0
% 2.46/1.41  #Close   : 0
% 2.46/1.41  
% 2.46/1.41  Ordering : KBO
% 2.46/1.41  
% 2.46/1.41  Simplification rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Subsume      : 5
% 2.46/1.41  #Demod        : 33
% 2.46/1.41  #Tautology    : 42
% 2.46/1.41  #SimpNegUnit  : 4
% 2.46/1.41  #BackRed      : 4
% 2.46/1.41  
% 2.46/1.42  #Partial instantiations: 0
% 2.46/1.42  #Strategies tried      : 1
% 2.46/1.42  
% 2.46/1.42  Timing (in seconds)
% 2.46/1.42  ----------------------
% 2.84/1.42  Preprocessing        : 0.34
% 2.84/1.42  Parsing              : 0.18
% 2.84/1.42  CNF conversion       : 0.02
% 2.84/1.42  Main loop            : 0.27
% 2.84/1.42  Inferencing          : 0.10
% 2.84/1.42  Reduction            : 0.09
% 2.84/1.42  Demodulation         : 0.06
% 2.84/1.42  BG Simplification    : 0.02
% 2.84/1.42  Subsumption          : 0.05
% 2.84/1.42  Abstraction          : 0.01
% 2.84/1.42  MUC search           : 0.00
% 2.84/1.42  Cooper               : 0.00
% 2.84/1.42  Total                : 0.64
% 2.84/1.42  Index Insertion      : 0.00
% 2.84/1.42  Index Deletion       : 0.00
% 2.84/1.42  Index Matching       : 0.00
% 2.84/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
