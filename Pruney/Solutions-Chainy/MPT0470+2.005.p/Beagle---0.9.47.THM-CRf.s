%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:01 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 118 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 188 expanded)
%              Number of equality atoms :   37 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_98,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_56,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_88,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [A_55] :
      ( v1_relat_1(A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_73,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_44,plain,(
    ! [A_45,B_46] :
      ( v1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [B_41] : k2_zfmisc_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_244,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_98,B_99)),k1_relat_1(A_98))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_255,plain,(
    ! [B_99] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_99)),k1_xboole_0)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_244])).

tff(c_261,plain,(
    ! [B_100] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_100)),k1_xboole_0)
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_255])).

tff(c_148,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_162,plain,(
    ! [B_77,A_76] :
      ( B_77 = A_76
      | ~ r1_tarski(B_77,A_76)
      | ~ v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_159,c_14])).

tff(c_267,plain,(
    ! [B_100] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_100)) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_261,c_162])).

tff(c_289,plain,(
    ! [B_102] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_102)) = k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_267])).

tff(c_46,plain,(
    ! [A_47] :
      ( k3_xboole_0(A_47,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47))) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_307,plain,(
    ! [B_102] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_102),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_102)))) = k5_relat_1(k1_xboole_0,B_102)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_102))
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_46])).

tff(c_440,plain,(
    ! [B_125] :
      ( k5_relat_1(k1_xboole_0,B_125) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_125))
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_38,c_307])).

tff(c_444,plain,(
    ! [B_46] :
      ( k5_relat_1(k1_xboole_0,B_46) = k1_xboole_0
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_440])).

tff(c_448,plain,(
    ! [B_126] :
      ( k5_relat_1(k1_xboole_0,B_126) = k1_xboole_0
      | ~ v1_relat_1(B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_444])).

tff(c_463,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_448])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_463])).

tff(c_472,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_36,plain,(
    ! [A_40] : k2_zfmisc_1(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_733,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_169,B_170)),k2_relat_1(B_170))
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_747,plain,(
    ! [A_169] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_169,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_733])).

tff(c_772,plain,(
    ! [A_171] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_171,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_747])).

tff(c_542,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_2'(A_143,B_144),A_143)
      | r1_tarski(A_143,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_553,plain,(
    ! [A_145,B_146] :
      ( ~ v1_xboole_0(A_145)
      | r1_tarski(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_542,c_2])).

tff(c_556,plain,(
    ! [B_146,A_145] :
      ( B_146 = A_145
      | ~ r1_tarski(B_146,A_145)
      | ~ v1_xboole_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_553,c_14])).

tff(c_778,plain,(
    ! [A_171] :
      ( k2_relat_1(k5_relat_1(A_171,k1_xboole_0)) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(A_171) ) ),
    inference(resolution,[status(thm)],[c_772,c_556])).

tff(c_800,plain,(
    ! [A_173] :
      ( k2_relat_1(k5_relat_1(A_173,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_778])).

tff(c_818,plain,(
    ! [A_173] :
      ( k3_xboole_0(k5_relat_1(A_173,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_173,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_173,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_173,k1_xboole_0))
      | ~ v1_relat_1(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_46])).

tff(c_872,plain,(
    ! [A_188] :
      ( k5_relat_1(A_188,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_188,k1_xboole_0))
      | ~ v1_relat_1(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36,c_818])).

tff(c_876,plain,(
    ! [A_45] :
      ( k5_relat_1(A_45,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_44,c_872])).

tff(c_880,plain,(
    ! [A_189] :
      ( k5_relat_1(A_189,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_876])).

tff(c_895,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_880])).

tff(c_903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:07:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.43  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.73/1.43  
% 2.73/1.43  %Foreground sorts:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Background operators:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Foreground operators:
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.43  
% 2.73/1.45  tff(f_105, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.73/1.45  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.73/1.45  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.73/1.45  tff(f_77, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.73/1.45  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.73/1.45  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.73/1.45  tff(f_98, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.73/1.45  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.73/1.45  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.73/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.73/1.45  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.45  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.73/1.45  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.73/1.45  tff(c_56, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.73/1.45  tff(c_88, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 2.73/1.45  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.73/1.45  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.45  tff(c_69, plain, (![A_55]: (v1_relat_1(A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.73/1.45  tff(c_73, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_69])).
% 2.73/1.45  tff(c_44, plain, (![A_45, B_46]: (v1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.45  tff(c_20, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.45  tff(c_38, plain, (![B_41]: (k2_zfmisc_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.45  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.73/1.45  tff(c_244, plain, (![A_98, B_99]: (r1_tarski(k1_relat_1(k5_relat_1(A_98, B_99)), k1_relat_1(A_98)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.45  tff(c_255, plain, (![B_99]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_99)), k1_xboole_0) | ~v1_relat_1(B_99) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_244])).
% 2.73/1.45  tff(c_261, plain, (![B_100]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_100)), k1_xboole_0) | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_255])).
% 2.73/1.45  tff(c_148, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.45  tff(c_159, plain, (![A_76, B_77]: (~v1_xboole_0(A_76) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_148, c_2])).
% 2.73/1.45  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.73/1.45  tff(c_162, plain, (![B_77, A_76]: (B_77=A_76 | ~r1_tarski(B_77, A_76) | ~v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_159, c_14])).
% 2.73/1.45  tff(c_267, plain, (![B_100]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_100))=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_261, c_162])).
% 2.73/1.45  tff(c_289, plain, (![B_102]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_102))=k1_xboole_0 | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_267])).
% 2.73/1.45  tff(c_46, plain, (![A_47]: (k3_xboole_0(A_47, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47)))=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.73/1.45  tff(c_307, plain, (![B_102]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_102), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_102))))=k5_relat_1(k1_xboole_0, B_102) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_102)) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_289, c_46])).
% 2.73/1.45  tff(c_440, plain, (![B_125]: (k5_relat_1(k1_xboole_0, B_125)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_125)) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_38, c_307])).
% 2.73/1.45  tff(c_444, plain, (![B_46]: (k5_relat_1(k1_xboole_0, B_46)=k1_xboole_0 | ~v1_relat_1(B_46) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_440])).
% 2.73/1.45  tff(c_448, plain, (![B_126]: (k5_relat_1(k1_xboole_0, B_126)=k1_xboole_0 | ~v1_relat_1(B_126))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_444])).
% 2.73/1.45  tff(c_463, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_448])).
% 2.73/1.45  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_463])).
% 2.73/1.45  tff(c_472, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.73/1.45  tff(c_36, plain, (![A_40]: (k2_zfmisc_1(A_40, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.45  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.73/1.45  tff(c_733, plain, (![A_169, B_170]: (r1_tarski(k2_relat_1(k5_relat_1(A_169, B_170)), k2_relat_1(B_170)) | ~v1_relat_1(B_170) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.73/1.45  tff(c_747, plain, (![A_169]: (r1_tarski(k2_relat_1(k5_relat_1(A_169, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_169))), inference(superposition, [status(thm), theory('equality')], [c_52, c_733])).
% 2.73/1.45  tff(c_772, plain, (![A_171]: (r1_tarski(k2_relat_1(k5_relat_1(A_171, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_747])).
% 2.73/1.45  tff(c_542, plain, (![A_143, B_144]: (r2_hidden('#skF_2'(A_143, B_144), A_143) | r1_tarski(A_143, B_144))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.45  tff(c_553, plain, (![A_145, B_146]: (~v1_xboole_0(A_145) | r1_tarski(A_145, B_146))), inference(resolution, [status(thm)], [c_542, c_2])).
% 2.73/1.45  tff(c_556, plain, (![B_146, A_145]: (B_146=A_145 | ~r1_tarski(B_146, A_145) | ~v1_xboole_0(A_145))), inference(resolution, [status(thm)], [c_553, c_14])).
% 2.73/1.45  tff(c_778, plain, (![A_171]: (k2_relat_1(k5_relat_1(A_171, k1_xboole_0))=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(A_171))), inference(resolution, [status(thm)], [c_772, c_556])).
% 2.73/1.45  tff(c_800, plain, (![A_173]: (k2_relat_1(k5_relat_1(A_173, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_778])).
% 2.73/1.45  tff(c_818, plain, (![A_173]: (k3_xboole_0(k5_relat_1(A_173, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_173, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_173, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_173, k1_xboole_0)) | ~v1_relat_1(A_173))), inference(superposition, [status(thm), theory('equality')], [c_800, c_46])).
% 2.73/1.45  tff(c_872, plain, (![A_188]: (k5_relat_1(A_188, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_188, k1_xboole_0)) | ~v1_relat_1(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_36, c_818])).
% 2.73/1.45  tff(c_876, plain, (![A_45]: (k5_relat_1(A_45, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_44, c_872])).
% 2.73/1.45  tff(c_880, plain, (![A_189]: (k5_relat_1(A_189, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_189))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_876])).
% 2.73/1.45  tff(c_895, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_880])).
% 2.73/1.45  tff(c_903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_895])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 0
% 2.73/1.45  #Sup     : 190
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 2
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 11
% 2.73/1.45  #Demod        : 89
% 2.73/1.45  #Tautology    : 98
% 2.73/1.45  #SimpNegUnit  : 2
% 2.73/1.45  #BackRed      : 0
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 0
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.73/1.45  Preprocessing        : 0.31
% 2.73/1.45  Parsing              : 0.17
% 2.73/1.45  CNF conversion       : 0.02
% 2.73/1.45  Main loop            : 0.34
% 2.73/1.45  Inferencing          : 0.13
% 2.73/1.45  Reduction            : 0.09
% 2.73/1.45  Demodulation         : 0.07
% 2.73/1.45  BG Simplification    : 0.02
% 2.73/1.45  Subsumption          : 0.06
% 2.73/1.45  Abstraction          : 0.02
% 2.73/1.45  MUC search           : 0.00
% 2.73/1.45  Cooper               : 0.00
% 2.73/1.45  Total                : 0.69
% 2.73/1.45  Index Insertion      : 0.00
% 2.73/1.45  Index Deletion       : 0.00
% 2.73/1.45  Index Matching       : 0.00
% 2.73/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
