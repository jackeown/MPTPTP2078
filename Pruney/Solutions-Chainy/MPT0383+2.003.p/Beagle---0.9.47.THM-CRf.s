%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:07 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 395 expanded)
%              Number of leaves         :   23 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 ( 990 expanded)
%              Number of equality atoms :    6 (  74 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_32,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_33,plain,(
    ! [B_27,A_28] :
      ( ~ r2_hidden(B_27,A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_33])).

tff(c_49,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(B_34,A_35)
      | ~ r2_hidden(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_55,plain,
    ( m1_subset_1('#skF_8','#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_59,plain,(
    m1_subset_1('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_55])).

tff(c_85,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_2'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_30,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_100,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_8',B_51)
      | ~ r1_tarski('#skF_7',B_51) ) ),
    inference(resolution,[status(thm)],[c_32,c_100])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_190,plain,(
    ! [B_58,B_59] :
      ( r2_hidden('#skF_8',B_58)
      | ~ r1_tarski(B_59,B_58)
      | ~ r1_tarski('#skF_7',B_59) ) ),
    inference(resolution,[status(thm)],[c_114,c_6])).

tff(c_196,plain,
    ( r2_hidden('#skF_8',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_190])).

tff(c_201,plain,(
    r2_hidden('#skF_8',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_196])).

tff(c_316,plain,(
    ! [A_85,B_86,C_87] :
      ( k4_tarski('#skF_3'(A_85,B_86,C_87),'#skF_4'(A_85,B_86,C_87)) = A_85
      | ~ r2_hidden(A_85,k2_zfmisc_1(B_86,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [E_24,F_26] :
      ( k4_tarski(E_24,F_26) != '#skF_8'
      | ~ m1_subset_1(F_26,'#skF_6')
      | ~ m1_subset_1(E_24,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_365,plain,(
    ! [A_93,B_94,C_95] :
      ( A_93 != '#skF_8'
      | ~ m1_subset_1('#skF_4'(A_93,B_94,C_95),'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_93,B_94,C_95),'#skF_5')
      | ~ r2_hidden(A_93,k2_zfmisc_1(B_94,C_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_28])).

tff(c_397,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_5','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_201,c_365])).

tff(c_508,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,A_19)
      | ~ v1_xboole_0(B_20)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_512,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_8','#skF_5','#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_508])).

tff(c_513,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k4_tarski('#skF_3'(A_10,B_11,C_12),'#skF_4'(A_10,B_11,C_12)) = A_10
      | ~ r2_hidden(A_10,k2_zfmisc_1(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r2_hidden(B_20,A_19)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_275,plain,(
    ! [B_81,B_82,A_83] :
      ( r2_hidden(B_81,B_82)
      | ~ r1_tarski(A_83,B_82)
      | ~ m1_subset_1(B_81,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_281,plain,(
    ! [B_81] :
      ( r2_hidden(B_81,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_81,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_275])).

tff(c_287,plain,(
    ! [B_84] :
      ( r2_hidden(B_84,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_84,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_281])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16,D_18] :
      ( r2_hidden(A_15,C_17)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_336,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(A_88,'#skF_5')
      | ~ m1_subset_1(k4_tarski(A_88,B_89),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_287,c_18])).

tff(c_734,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_hidden('#skF_3'(A_145,B_146,C_147),'#skF_5')
      | ~ m1_subset_1(A_145,'#skF_7')
      | ~ r2_hidden(A_145,k2_zfmisc_1(B_146,C_147)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_336])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,A_19)
      | ~ r2_hidden(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_739,plain,(
    ! [A_145,B_146,C_147] :
      ( m1_subset_1('#skF_3'(A_145,B_146,C_147),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_145,'#skF_7')
      | ~ r2_hidden(A_145,k2_zfmisc_1(B_146,C_147)) ) ),
    inference(resolution,[status(thm)],[c_734,c_20])).

tff(c_803,plain,(
    ! [A_155,B_156,C_157] :
      ( m1_subset_1('#skF_3'(A_155,B_156,C_157),'#skF_5')
      | ~ m1_subset_1(A_155,'#skF_7')
      | ~ r2_hidden(A_155,k2_zfmisc_1(B_156,C_157)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_739])).

tff(c_830,plain,
    ( m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_803])).

tff(c_860,plain,(
    m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_830])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_860])).

tff(c_864,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_1025,plain,(
    ! [A_176,B_177,C_178] :
      ( r2_hidden('#skF_3'(A_176,B_177,C_178),'#skF_5')
      | ~ m1_subset_1(A_176,'#skF_7')
      | ~ r2_hidden(A_176,k2_zfmisc_1(B_177,C_178)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_336])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1033,plain,(
    ! [A_176,B_177,C_178] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_176,'#skF_7')
      | ~ r2_hidden(A_176,k2_zfmisc_1(B_177,C_178)) ) ),
    inference(resolution,[status(thm)],[c_1025,c_2])).

tff(c_1080,plain,(
    ! [A_184,B_185,C_186] :
      ( ~ m1_subset_1(A_184,'#skF_7')
      | ~ r2_hidden(A_184,k2_zfmisc_1(B_185,C_186)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_1033])).

tff(c_1099,plain,(
    ~ m1_subset_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_1080])).

tff(c_1128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1099])).

tff(c_1129,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_1134,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_8','#skF_5','#skF_6'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_1129])).

tff(c_1156,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1134])).

tff(c_16,plain,(
    ! [B_16,D_18,A_15,C_17] :
      ( r2_hidden(B_16,D_18)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_356,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,'#skF_6')
      | ~ m1_subset_1(k4_tarski(A_92,B_91),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_287,c_16])).

tff(c_1390,plain,(
    ! [A_218,B_219,C_220] :
      ( r2_hidden('#skF_4'(A_218,B_219,C_220),'#skF_6')
      | ~ m1_subset_1(A_218,'#skF_7')
      | ~ r2_hidden(A_218,k2_zfmisc_1(B_219,C_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_356])).

tff(c_1395,plain,(
    ! [A_218,B_219,C_220] :
      ( m1_subset_1('#skF_4'(A_218,B_219,C_220),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_218,'#skF_7')
      | ~ r2_hidden(A_218,k2_zfmisc_1(B_219,C_220)) ) ),
    inference(resolution,[status(thm)],[c_1390,c_20])).

tff(c_1459,plain,(
    ! [A_228,B_229,C_230] :
      ( m1_subset_1('#skF_4'(A_228,B_229,C_230),'#skF_6')
      | ~ m1_subset_1(A_228,'#skF_7')
      | ~ r2_hidden(A_228,k2_zfmisc_1(B_229,C_230)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1156,c_1395])).

tff(c_1486,plain,
    ( m1_subset_1('#skF_4'('#skF_8','#skF_5','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_1459])).

tff(c_1516,plain,(
    m1_subset_1('#skF_4'('#skF_8','#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1486])).

tff(c_1518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1129,c_1516])).

tff(c_1520,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1134])).

tff(c_1762,plain,(
    ! [A_261,B_262,C_263] :
      ( r2_hidden('#skF_4'(A_261,B_262,C_263),'#skF_6')
      | ~ m1_subset_1(A_261,'#skF_7')
      | ~ r2_hidden(A_261,k2_zfmisc_1(B_262,C_263)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_356])).

tff(c_1770,plain,(
    ! [A_261,B_262,C_263] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_261,'#skF_7')
      | ~ r2_hidden(A_261,k2_zfmisc_1(B_262,C_263)) ) ),
    inference(resolution,[status(thm)],[c_1762,c_2])).

tff(c_1821,plain,(
    ! [A_269,B_270,C_271] :
      ( ~ m1_subset_1(A_269,'#skF_7')
      | ~ r2_hidden(A_269,k2_zfmisc_1(B_270,C_271)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_1770])).

tff(c_1844,plain,(
    ~ m1_subset_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_1821])).

tff(c_1874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:32:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.58  
% 3.61/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.58  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 3.61/1.58  
% 3.61/1.58  %Foreground sorts:
% 3.61/1.58  
% 3.61/1.58  
% 3.61/1.58  %Background operators:
% 3.61/1.58  
% 3.61/1.58  
% 3.61/1.58  %Foreground operators:
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.61/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.61/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.61/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.61/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.61/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.61/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.61/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.58  
% 3.61/1.60  tff(f_79, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 3.61/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.61/1.60  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.61/1.60  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.61/1.60  tff(f_45, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.61/1.60  tff(f_51, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.61/1.60  tff(c_32, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.61/1.60  tff(c_33, plain, (![B_27, A_28]: (~r2_hidden(B_27, A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.60  tff(c_37, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_32, c_33])).
% 3.61/1.60  tff(c_49, plain, (![B_34, A_35]: (m1_subset_1(B_34, A_35) | ~r2_hidden(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.60  tff(c_55, plain, (m1_subset_1('#skF_8', '#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_32, c_49])).
% 3.61/1.60  tff(c_59, plain, (m1_subset_1('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_37, c_55])).
% 3.61/1.60  tff(c_85, plain, (![A_43, B_44]: (r2_hidden('#skF_2'(A_43, B_44), A_43) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.61/1.60  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.61/1.60  tff(c_96, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_85, c_8])).
% 3.61/1.60  tff(c_30, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.61/1.60  tff(c_100, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.61/1.60  tff(c_114, plain, (![B_51]: (r2_hidden('#skF_8', B_51) | ~r1_tarski('#skF_7', B_51))), inference(resolution, [status(thm)], [c_32, c_100])).
% 3.61/1.60  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.61/1.60  tff(c_190, plain, (![B_58, B_59]: (r2_hidden('#skF_8', B_58) | ~r1_tarski(B_59, B_58) | ~r1_tarski('#skF_7', B_59))), inference(resolution, [status(thm)], [c_114, c_6])).
% 3.61/1.60  tff(c_196, plain, (r2_hidden('#skF_8', k2_zfmisc_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_30, c_190])).
% 3.61/1.60  tff(c_201, plain, (r2_hidden('#skF_8', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_196])).
% 3.61/1.60  tff(c_316, plain, (![A_85, B_86, C_87]: (k4_tarski('#skF_3'(A_85, B_86, C_87), '#skF_4'(A_85, B_86, C_87))=A_85 | ~r2_hidden(A_85, k2_zfmisc_1(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.61/1.60  tff(c_28, plain, (![E_24, F_26]: (k4_tarski(E_24, F_26)!='#skF_8' | ~m1_subset_1(F_26, '#skF_6') | ~m1_subset_1(E_24, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.61/1.60  tff(c_365, plain, (![A_93, B_94, C_95]: (A_93!='#skF_8' | ~m1_subset_1('#skF_4'(A_93, B_94, C_95), '#skF_6') | ~m1_subset_1('#skF_3'(A_93, B_94, C_95), '#skF_5') | ~r2_hidden(A_93, k2_zfmisc_1(B_94, C_95)))), inference(superposition, [status(thm), theory('equality')], [c_316, c_28])).
% 3.61/1.60  tff(c_397, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_5', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_201, c_365])).
% 3.61/1.60  tff(c_508, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_397])).
% 3.61/1.60  tff(c_24, plain, (![B_20, A_19]: (m1_subset_1(B_20, A_19) | ~v1_xboole_0(B_20) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.60  tff(c_512, plain, (~v1_xboole_0('#skF_3'('#skF_8', '#skF_5', '#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_508])).
% 3.61/1.60  tff(c_513, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_512])).
% 3.61/1.60  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_tarski('#skF_3'(A_10, B_11, C_12), '#skF_4'(A_10, B_11, C_12))=A_10 | ~r2_hidden(A_10, k2_zfmisc_1(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.61/1.60  tff(c_22, plain, (![B_20, A_19]: (r2_hidden(B_20, A_19) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.60  tff(c_275, plain, (![B_81, B_82, A_83]: (r2_hidden(B_81, B_82) | ~r1_tarski(A_83, B_82) | ~m1_subset_1(B_81, A_83) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_22, c_100])).
% 3.61/1.60  tff(c_281, plain, (![B_81]: (r2_hidden(B_81, k2_zfmisc_1('#skF_5', '#skF_6')) | ~m1_subset_1(B_81, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_275])).
% 3.61/1.60  tff(c_287, plain, (![B_84]: (r2_hidden(B_84, k2_zfmisc_1('#skF_5', '#skF_6')) | ~m1_subset_1(B_84, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_37, c_281])).
% 3.61/1.60  tff(c_18, plain, (![A_15, C_17, B_16, D_18]: (r2_hidden(A_15, C_17) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.61/1.60  tff(c_336, plain, (![A_88, B_89]: (r2_hidden(A_88, '#skF_5') | ~m1_subset_1(k4_tarski(A_88, B_89), '#skF_7'))), inference(resolution, [status(thm)], [c_287, c_18])).
% 3.61/1.60  tff(c_734, plain, (![A_145, B_146, C_147]: (r2_hidden('#skF_3'(A_145, B_146, C_147), '#skF_5') | ~m1_subset_1(A_145, '#skF_7') | ~r2_hidden(A_145, k2_zfmisc_1(B_146, C_147)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_336])).
% 3.61/1.60  tff(c_20, plain, (![B_20, A_19]: (m1_subset_1(B_20, A_19) | ~r2_hidden(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.60  tff(c_739, plain, (![A_145, B_146, C_147]: (m1_subset_1('#skF_3'(A_145, B_146, C_147), '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(A_145, '#skF_7') | ~r2_hidden(A_145, k2_zfmisc_1(B_146, C_147)))), inference(resolution, [status(thm)], [c_734, c_20])).
% 3.61/1.60  tff(c_803, plain, (![A_155, B_156, C_157]: (m1_subset_1('#skF_3'(A_155, B_156, C_157), '#skF_5') | ~m1_subset_1(A_155, '#skF_7') | ~r2_hidden(A_155, k2_zfmisc_1(B_156, C_157)))), inference(negUnitSimplification, [status(thm)], [c_513, c_739])).
% 3.61/1.60  tff(c_830, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_201, c_803])).
% 3.61/1.60  tff(c_860, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_830])).
% 3.61/1.60  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_860])).
% 3.61/1.60  tff(c_864, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_512])).
% 3.61/1.60  tff(c_1025, plain, (![A_176, B_177, C_178]: (r2_hidden('#skF_3'(A_176, B_177, C_178), '#skF_5') | ~m1_subset_1(A_176, '#skF_7') | ~r2_hidden(A_176, k2_zfmisc_1(B_177, C_178)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_336])).
% 3.61/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.60  tff(c_1033, plain, (![A_176, B_177, C_178]: (~v1_xboole_0('#skF_5') | ~m1_subset_1(A_176, '#skF_7') | ~r2_hidden(A_176, k2_zfmisc_1(B_177, C_178)))), inference(resolution, [status(thm)], [c_1025, c_2])).
% 3.61/1.60  tff(c_1080, plain, (![A_184, B_185, C_186]: (~m1_subset_1(A_184, '#skF_7') | ~r2_hidden(A_184, k2_zfmisc_1(B_185, C_186)))), inference(demodulation, [status(thm), theory('equality')], [c_864, c_1033])).
% 3.61/1.60  tff(c_1099, plain, (~m1_subset_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_201, c_1080])).
% 3.61/1.60  tff(c_1128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_1099])).
% 3.61/1.60  tff(c_1129, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_397])).
% 3.61/1.60  tff(c_1134, plain, (~v1_xboole_0('#skF_4'('#skF_8', '#skF_5', '#skF_6')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_24, c_1129])).
% 3.61/1.60  tff(c_1156, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1134])).
% 3.61/1.60  tff(c_16, plain, (![B_16, D_18, A_15, C_17]: (r2_hidden(B_16, D_18) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.61/1.60  tff(c_356, plain, (![B_91, A_92]: (r2_hidden(B_91, '#skF_6') | ~m1_subset_1(k4_tarski(A_92, B_91), '#skF_7'))), inference(resolution, [status(thm)], [c_287, c_16])).
% 3.61/1.60  tff(c_1390, plain, (![A_218, B_219, C_220]: (r2_hidden('#skF_4'(A_218, B_219, C_220), '#skF_6') | ~m1_subset_1(A_218, '#skF_7') | ~r2_hidden(A_218, k2_zfmisc_1(B_219, C_220)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_356])).
% 3.61/1.60  tff(c_1395, plain, (![A_218, B_219, C_220]: (m1_subset_1('#skF_4'(A_218, B_219, C_220), '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_218, '#skF_7') | ~r2_hidden(A_218, k2_zfmisc_1(B_219, C_220)))), inference(resolution, [status(thm)], [c_1390, c_20])).
% 3.61/1.60  tff(c_1459, plain, (![A_228, B_229, C_230]: (m1_subset_1('#skF_4'(A_228, B_229, C_230), '#skF_6') | ~m1_subset_1(A_228, '#skF_7') | ~r2_hidden(A_228, k2_zfmisc_1(B_229, C_230)))), inference(negUnitSimplification, [status(thm)], [c_1156, c_1395])).
% 3.61/1.60  tff(c_1486, plain, (m1_subset_1('#skF_4'('#skF_8', '#skF_5', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_201, c_1459])).
% 3.61/1.60  tff(c_1516, plain, (m1_subset_1('#skF_4'('#skF_8', '#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_1486])).
% 3.61/1.60  tff(c_1518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1129, c_1516])).
% 3.61/1.60  tff(c_1520, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_1134])).
% 3.61/1.60  tff(c_1762, plain, (![A_261, B_262, C_263]: (r2_hidden('#skF_4'(A_261, B_262, C_263), '#skF_6') | ~m1_subset_1(A_261, '#skF_7') | ~r2_hidden(A_261, k2_zfmisc_1(B_262, C_263)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_356])).
% 3.61/1.60  tff(c_1770, plain, (![A_261, B_262, C_263]: (~v1_xboole_0('#skF_6') | ~m1_subset_1(A_261, '#skF_7') | ~r2_hidden(A_261, k2_zfmisc_1(B_262, C_263)))), inference(resolution, [status(thm)], [c_1762, c_2])).
% 3.61/1.60  tff(c_1821, plain, (![A_269, B_270, C_271]: (~m1_subset_1(A_269, '#skF_7') | ~r2_hidden(A_269, k2_zfmisc_1(B_270, C_271)))), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_1770])).
% 3.61/1.60  tff(c_1844, plain, (~m1_subset_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_201, c_1821])).
% 3.61/1.60  tff(c_1874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_1844])).
% 3.61/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.60  
% 3.61/1.60  Inference rules
% 3.61/1.60  ----------------------
% 3.61/1.60  #Ref     : 0
% 3.61/1.60  #Sup     : 407
% 3.61/1.60  #Fact    : 0
% 3.61/1.60  #Define  : 0
% 3.61/1.60  #Split   : 13
% 3.61/1.60  #Chain   : 0
% 3.61/1.60  #Close   : 0
% 3.61/1.60  
% 3.61/1.60  Ordering : KBO
% 3.61/1.60  
% 3.61/1.60  Simplification rules
% 3.61/1.60  ----------------------
% 3.61/1.60  #Subsume      : 138
% 3.61/1.60  #Demod        : 53
% 3.61/1.60  #Tautology    : 56
% 3.61/1.60  #SimpNegUnit  : 61
% 3.61/1.60  #BackRed      : 0
% 3.61/1.60  
% 3.61/1.60  #Partial instantiations: 0
% 3.61/1.60  #Strategies tried      : 1
% 3.61/1.60  
% 3.61/1.60  Timing (in seconds)
% 3.61/1.60  ----------------------
% 3.61/1.61  Preprocessing        : 0.27
% 3.61/1.61  Parsing              : 0.15
% 3.61/1.61  CNF conversion       : 0.02
% 3.61/1.61  Main loop            : 0.56
% 3.61/1.61  Inferencing          : 0.21
% 3.61/1.61  Reduction            : 0.15
% 3.61/1.61  Demodulation         : 0.09
% 3.61/1.61  BG Simplification    : 0.02
% 3.61/1.61  Subsumption          : 0.14
% 3.61/1.61  Abstraction          : 0.02
% 3.61/1.61  MUC search           : 0.00
% 3.61/1.61  Cooper               : 0.00
% 3.61/1.61  Total                : 0.87
% 3.61/1.61  Index Insertion      : 0.00
% 3.61/1.61  Index Deletion       : 0.00
% 3.61/1.61  Index Matching       : 0.00
% 3.61/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
