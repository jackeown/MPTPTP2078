%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:03 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 166 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 333 expanded)
%              Number of equality atoms :   32 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_92,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_241,plain,(
    ! [B_113,A_114] :
      ( k1_tarski(k1_funct_1(B_113,A_114)) = k2_relat_1(B_113)
      | k1_tarski(A_114) != k1_relat_1(B_113)
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_192,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_199,plain,(
    ! [D_99] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_99) = k9_relat_1('#skF_4',D_99) ),
    inference(resolution,[status(thm)],[c_56,c_192])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_200,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_52])).

tff(c_247,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_200])).

tff(c_253,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_60,c_247])).

tff(c_255,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_143,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_152,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_143])).

tff(c_655,plain,(
    ! [B_186,A_187,C_188] :
      ( k1_xboole_0 = B_186
      | k1_relset_1(A_187,B_186,C_188) = A_187
      | ~ v1_funct_2(C_188,A_187,B_186)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_669,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_655])).

tff(c_675,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_152,c_669])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_54,c_675])).

tff(c_679,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_684,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_56])).

tff(c_946,plain,(
    ! [D_235,C_236,B_237,A_238] :
      ( m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(C_236,B_237)))
      | ~ r1_tarski(k2_relat_1(D_235),B_237)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(C_236,A_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_958,plain,(
    ! [B_239] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_239)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_239) ) ),
    inference(resolution,[status(thm)],[c_684,c_946])).

tff(c_36,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k7_relset_1(A_47,B_48,C_49,D_50) = k9_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1069,plain,(
    ! [B_251,D_252] :
      ( k7_relset_1(k1_relat_1('#skF_4'),B_251,'#skF_4',D_252) = k9_relat_1('#skF_4',D_252)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_251) ) ),
    inference(resolution,[status(thm)],[c_958,c_36])).

tff(c_1074,plain,(
    ! [D_253] : k7_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4',D_253) = k9_relat_1('#skF_4',D_253) ),
    inference(resolution,[status(thm)],[c_6,c_1069])).

tff(c_729,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( m1_subset_1(k7_relset_1(A_189,B_190,C_191,D_192),k1_zfmisc_1(B_190))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_754,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( r1_tarski(k7_relset_1(A_189,B_190,C_191,D_192),B_190)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(resolution,[status(thm)],[c_729,c_22])).

tff(c_982,plain,(
    ! [B_239,D_192] :
      ( r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),B_239,'#skF_4',D_192),B_239)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_239) ) ),
    inference(resolution,[status(thm)],[c_958,c_754])).

tff(c_1080,plain,(
    ! [D_253] :
      ( r1_tarski(k9_relat_1('#skF_4',D_253),k2_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_982])).

tff(c_1092,plain,(
    ! [D_253] : r1_tarski(k9_relat_1('#skF_4',D_253),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1080])).

tff(c_678,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:36:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.50  
% 3.38/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.50  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.38/1.50  
% 3.38/1.50  %Foreground sorts:
% 3.38/1.50  
% 3.38/1.50  
% 3.38/1.50  %Background operators:
% 3.38/1.50  
% 3.38/1.50  
% 3.38/1.50  %Foreground operators:
% 3.38/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.38/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.38/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.38/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.38/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.38/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.38/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.38/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.50  
% 3.50/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.50/1.52  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.50/1.52  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.50/1.52  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.50/1.52  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.50/1.52  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.50/1.52  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.50/1.52  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.50/1.52  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 3.50/1.52  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.50/1.52  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.50/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.52  tff(c_28, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.52  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.50/1.52  tff(c_92, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.50/1.52  tff(c_98, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_92])).
% 3.50/1.52  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_98])).
% 3.50/1.52  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.50/1.52  tff(c_241, plain, (![B_113, A_114]: (k1_tarski(k1_funct_1(B_113, A_114))=k2_relat_1(B_113) | k1_tarski(A_114)!=k1_relat_1(B_113) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.50/1.52  tff(c_192, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.50/1.52  tff(c_199, plain, (![D_99]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_99)=k9_relat_1('#skF_4', D_99))), inference(resolution, [status(thm)], [c_56, c_192])).
% 3.50/1.52  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.50/1.52  tff(c_200, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_52])).
% 3.50/1.52  tff(c_247, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_241, c_200])).
% 3.50/1.52  tff(c_253, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_60, c_247])).
% 3.50/1.52  tff(c_255, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_253])).
% 3.50/1.52  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.50/1.52  tff(c_58, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.50/1.52  tff(c_143, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.50/1.52  tff(c_152, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_143])).
% 3.50/1.52  tff(c_655, plain, (![B_186, A_187, C_188]: (k1_xboole_0=B_186 | k1_relset_1(A_187, B_186, C_188)=A_187 | ~v1_funct_2(C_188, A_187, B_186) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.50/1.52  tff(c_669, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_655])).
% 3.50/1.52  tff(c_675, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_152, c_669])).
% 3.50/1.52  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_54, c_675])).
% 3.50/1.52  tff(c_679, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_253])).
% 3.50/1.52  tff(c_684, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_56])).
% 3.50/1.52  tff(c_946, plain, (![D_235, C_236, B_237, A_238]: (m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(C_236, B_237))) | ~r1_tarski(k2_relat_1(D_235), B_237) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(C_236, A_238))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.50/1.52  tff(c_958, plain, (![B_239]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_239))) | ~r1_tarski(k2_relat_1('#skF_4'), B_239))), inference(resolution, [status(thm)], [c_684, c_946])).
% 3.50/1.52  tff(c_36, plain, (![A_47, B_48, C_49, D_50]: (k7_relset_1(A_47, B_48, C_49, D_50)=k9_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.50/1.52  tff(c_1069, plain, (![B_251, D_252]: (k7_relset_1(k1_relat_1('#skF_4'), B_251, '#skF_4', D_252)=k9_relat_1('#skF_4', D_252) | ~r1_tarski(k2_relat_1('#skF_4'), B_251))), inference(resolution, [status(thm)], [c_958, c_36])).
% 3.50/1.52  tff(c_1074, plain, (![D_253]: (k7_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', D_253)=k9_relat_1('#skF_4', D_253))), inference(resolution, [status(thm)], [c_6, c_1069])).
% 3.50/1.52  tff(c_729, plain, (![A_189, B_190, C_191, D_192]: (m1_subset_1(k7_relset_1(A_189, B_190, C_191, D_192), k1_zfmisc_1(B_190)) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.50/1.52  tff(c_22, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.50/1.52  tff(c_754, plain, (![A_189, B_190, C_191, D_192]: (r1_tarski(k7_relset_1(A_189, B_190, C_191, D_192), B_190) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(resolution, [status(thm)], [c_729, c_22])).
% 3.50/1.52  tff(c_982, plain, (![B_239, D_192]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), B_239, '#skF_4', D_192), B_239) | ~r1_tarski(k2_relat_1('#skF_4'), B_239))), inference(resolution, [status(thm)], [c_958, c_754])).
% 3.50/1.52  tff(c_1080, plain, (![D_253]: (r1_tarski(k9_relat_1('#skF_4', D_253), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1074, c_982])).
% 3.50/1.52  tff(c_1092, plain, (![D_253]: (r1_tarski(k9_relat_1('#skF_4', D_253), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1080])).
% 3.50/1.52  tff(c_678, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_253])).
% 3.50/1.52  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1092, c_678])).
% 3.50/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.52  
% 3.50/1.52  Inference rules
% 3.50/1.52  ----------------------
% 3.50/1.52  #Ref     : 0
% 3.50/1.52  #Sup     : 227
% 3.50/1.52  #Fact    : 0
% 3.50/1.52  #Define  : 0
% 3.50/1.52  #Split   : 5
% 3.50/1.52  #Chain   : 0
% 3.50/1.52  #Close   : 0
% 3.50/1.52  
% 3.50/1.52  Ordering : KBO
% 3.50/1.52  
% 3.50/1.52  Simplification rules
% 3.50/1.52  ----------------------
% 3.50/1.52  #Subsume      : 18
% 3.50/1.52  #Demod        : 63
% 3.50/1.52  #Tautology    : 69
% 3.50/1.52  #SimpNegUnit  : 1
% 3.50/1.52  #BackRed      : 8
% 3.50/1.52  
% 3.50/1.52  #Partial instantiations: 0
% 3.50/1.52  #Strategies tried      : 1
% 3.50/1.52  
% 3.50/1.52  Timing (in seconds)
% 3.50/1.52  ----------------------
% 3.50/1.52  Preprocessing        : 0.36
% 3.50/1.52  Parsing              : 0.18
% 3.50/1.52  CNF conversion       : 0.02
% 3.50/1.52  Main loop            : 0.43
% 3.50/1.52  Inferencing          : 0.16
% 3.50/1.52  Reduction            : 0.13
% 3.50/1.52  Demodulation         : 0.09
% 3.50/1.52  BG Simplification    : 0.03
% 3.50/1.52  Subsumption          : 0.08
% 3.50/1.52  Abstraction          : 0.03
% 3.50/1.52  MUC search           : 0.00
% 3.50/1.52  Cooper               : 0.00
% 3.50/1.52  Total                : 0.82
% 3.50/1.52  Index Insertion      : 0.00
% 3.50/1.52  Index Deletion       : 0.00
% 3.50/1.52  Index Matching       : 0.00
% 3.50/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
