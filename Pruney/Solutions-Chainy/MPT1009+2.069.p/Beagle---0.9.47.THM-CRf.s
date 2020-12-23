%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:51 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 222 expanded)
%              Number of leaves         :   41 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  100 ( 419 expanded)
%              Number of equality atoms :   35 ( 126 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_91,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_100,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,A_15),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_121,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_113,c_30])).

tff(c_133,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_168,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_181,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_168])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_192,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_181,c_26])).

tff(c_195,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_192])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_21)),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_247,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_32])).

tff(c_251,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_247])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_255,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_251,c_8])).

tff(c_258,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_255])).

tff(c_494,plain,(
    ! [B_113,A_114] :
      ( k1_tarski(k1_funct_1(B_113,A_114)) = k2_relat_1(B_113)
      | k1_tarski(A_114) != k1_relat_1(B_113)
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_264,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_48])).

tff(c_431,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k7_relset_1(A_94,B_95,C_96,D_97) = k9_relat_1(C_96,D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_440,plain,(
    ! [D_97] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_97) = k9_relat_1('#skF_4',D_97) ),
    inference(resolution,[status(thm)],[c_264,c_431])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_262,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_44])).

tff(c_452,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_262])).

tff(c_500,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_452])).

tff(c_515,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_52,c_258,c_500])).

tff(c_519,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_515])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_519])).

tff(c_524,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_533,plain,(
    ! [A_9] : r1_tarski('#skF_4',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_96])).

tff(c_24,plain,(
    ! [A_17] : k9_relat_1(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_536,plain,(
    ! [A_17] : k9_relat_1('#skF_4',A_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_524,c_24])).

tff(c_537,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_14])).

tff(c_763,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k7_relset_1(A_166,B_167,C_168,D_169) = k9_relat_1(C_168,D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_766,plain,(
    ! [A_166,B_167,D_169] : k7_relset_1(A_166,B_167,'#skF_4',D_169) = k9_relat_1('#skF_4',D_169) ),
    inference(resolution,[status(thm)],[c_537,c_763])).

tff(c_771,plain,(
    ! [A_166,B_167,D_169] : k7_relset_1(A_166,B_167,'#skF_4',D_169) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_766])).

tff(c_773,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_44])).

tff(c_776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:13:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.48  
% 2.96/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.49  
% 2.96/1.49  %Foreground sorts:
% 2.96/1.49  
% 2.96/1.49  
% 2.96/1.49  %Background operators:
% 2.96/1.49  
% 2.96/1.49  
% 2.96/1.49  %Foreground operators:
% 2.96/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.96/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.96/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.96/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.96/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.96/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.96/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.49  
% 3.05/1.50  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.05/1.50  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.05/1.50  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.05/1.50  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.05/1.50  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.05/1.50  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.05/1.50  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.05/1.50  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.05/1.50  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.05/1.50  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.05/1.50  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.05/1.50  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.50  tff(f_55, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.05/1.50  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.05/1.50  tff(c_100, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.05/1.50  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_100])).
% 3.05/1.50  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, A_15), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.05/1.50  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.05/1.50  tff(c_30, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.05/1.50  tff(c_121, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_113, c_30])).
% 3.05/1.50  tff(c_133, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_121])).
% 3.05/1.50  tff(c_168, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.05/1.50  tff(c_181, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_168])).
% 3.05/1.50  tff(c_26, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.05/1.50  tff(c_192, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_181, c_26])).
% 3.05/1.50  tff(c_195, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_192])).
% 3.05/1.50  tff(c_32, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_21)), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.05/1.50  tff(c_247, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_195, c_32])).
% 3.05/1.50  tff(c_251, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_247])).
% 3.05/1.50  tff(c_8, plain, (![B_8, A_7]: (k1_tarski(B_8)=A_7 | k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.50  tff(c_255, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_251, c_8])).
% 3.05/1.50  tff(c_258, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_133, c_255])).
% 3.05/1.50  tff(c_494, plain, (![B_113, A_114]: (k1_tarski(k1_funct_1(B_113, A_114))=k2_relat_1(B_113) | k1_tarski(A_114)!=k1_relat_1(B_113) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.05/1.50  tff(c_264, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_48])).
% 3.05/1.50  tff(c_431, plain, (![A_94, B_95, C_96, D_97]: (k7_relset_1(A_94, B_95, C_96, D_97)=k9_relat_1(C_96, D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.05/1.50  tff(c_440, plain, (![D_97]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_97)=k9_relat_1('#skF_4', D_97))), inference(resolution, [status(thm)], [c_264, c_431])).
% 3.05/1.50  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.05/1.50  tff(c_262, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_44])).
% 3.05/1.50  tff(c_452, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_262])).
% 3.05/1.50  tff(c_500, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_494, c_452])).
% 3.05/1.50  tff(c_515, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_52, c_258, c_500])).
% 3.05/1.50  tff(c_519, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_515])).
% 3.05/1.50  tff(c_523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_519])).
% 3.05/1.50  tff(c_524, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_121])).
% 3.05/1.50  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.50  tff(c_84, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.50  tff(c_96, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_14, c_84])).
% 3.05/1.50  tff(c_533, plain, (![A_9]: (r1_tarski('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_96])).
% 3.05/1.50  tff(c_24, plain, (![A_17]: (k9_relat_1(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.50  tff(c_536, plain, (![A_17]: (k9_relat_1('#skF_4', A_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_524, c_24])).
% 3.05/1.50  tff(c_537, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_14])).
% 3.05/1.50  tff(c_763, plain, (![A_166, B_167, C_168, D_169]: (k7_relset_1(A_166, B_167, C_168, D_169)=k9_relat_1(C_168, D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.05/1.50  tff(c_766, plain, (![A_166, B_167, D_169]: (k7_relset_1(A_166, B_167, '#skF_4', D_169)=k9_relat_1('#skF_4', D_169))), inference(resolution, [status(thm)], [c_537, c_763])).
% 3.05/1.50  tff(c_771, plain, (![A_166, B_167, D_169]: (k7_relset_1(A_166, B_167, '#skF_4', D_169)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_536, c_766])).
% 3.05/1.50  tff(c_773, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_44])).
% 3.05/1.50  tff(c_776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_533, c_773])).
% 3.05/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.50  
% 3.05/1.50  Inference rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Ref     : 0
% 3.05/1.50  #Sup     : 141
% 3.05/1.50  #Fact    : 0
% 3.05/1.50  #Define  : 0
% 3.05/1.50  #Split   : 4
% 3.05/1.50  #Chain   : 0
% 3.05/1.50  #Close   : 0
% 3.05/1.50  
% 3.05/1.50  Ordering : KBO
% 3.05/1.50  
% 3.05/1.50  Simplification rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Subsume      : 0
% 3.05/1.50  #Demod        : 106
% 3.05/1.50  #Tautology    : 87
% 3.05/1.50  #SimpNegUnit  : 3
% 3.05/1.50  #BackRed      : 18
% 3.05/1.50  
% 3.05/1.50  #Partial instantiations: 0
% 3.05/1.50  #Strategies tried      : 1
% 3.05/1.50  
% 3.05/1.50  Timing (in seconds)
% 3.05/1.50  ----------------------
% 3.05/1.50  Preprocessing        : 0.35
% 3.05/1.51  Parsing              : 0.19
% 3.05/1.51  CNF conversion       : 0.02
% 3.05/1.51  Main loop            : 0.33
% 3.05/1.51  Inferencing          : 0.13
% 3.05/1.51  Reduction            : 0.11
% 3.05/1.51  Demodulation         : 0.08
% 3.05/1.51  BG Simplification    : 0.02
% 3.05/1.51  Subsumption          : 0.04
% 3.05/1.51  Abstraction          : 0.02
% 3.05/1.51  MUC search           : 0.00
% 3.05/1.51  Cooper               : 0.00
% 3.05/1.51  Total                : 0.72
% 3.05/1.51  Index Insertion      : 0.00
% 3.05/1.51  Index Deletion       : 0.00
% 3.05/1.51  Index Matching       : 0.00
% 3.05/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
