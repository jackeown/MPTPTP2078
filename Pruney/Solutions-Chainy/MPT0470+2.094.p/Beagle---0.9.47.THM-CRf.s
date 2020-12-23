%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:14 EST 2020

% Result     : Theorem 11.99s
% Output     : CNFRefutation 12.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 189 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 ( 386 expanded)
%              Number of equality atoms :   24 (  72 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_30,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_36,plain,
    ( k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [B_131,A_132] :
      ( v1_relat_1(B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_132))
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_48,plain,(
    ! [A_4] : ~ v1_relat_1(A_4) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_354,plain,(
    ! [A_225,B_226,C_227] :
      ( r2_hidden(k4_tarski('#skF_4'(A_225,B_226,C_227),'#skF_6'(A_225,B_226,C_227)),A_225)
      | r2_hidden(k4_tarski('#skF_7'(A_225,B_226,C_227),'#skF_8'(A_225,B_226,C_227)),C_227)
      | k5_relat_1(A_225,B_226) = C_227
      | ~ v1_relat_1(C_227)
      | ~ v1_relat_1(B_226)
      | ~ v1_relat_1(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [C_26,D_27,B_21,A_11] :
      ( r2_hidden(k4_tarski(C_26,D_27),B_21)
      | ~ r2_hidden(k4_tarski(C_26,D_27),A_11)
      | ~ r1_tarski(A_11,B_21)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10023,plain,(
    ! [A_878,B_879,C_880,B_881] :
      ( r2_hidden(k4_tarski('#skF_4'(A_878,B_879,C_880),'#skF_6'(A_878,B_879,C_880)),B_881)
      | ~ r1_tarski(A_878,B_881)
      | r2_hidden(k4_tarski('#skF_7'(A_878,B_879,C_880),'#skF_8'(A_878,B_879,C_880)),C_880)
      | k5_relat_1(A_878,B_879) = C_880
      | ~ v1_relat_1(C_880)
      | ~ v1_relat_1(B_879)
      | ~ v1_relat_1(A_878) ) ),
    inference(resolution,[status(thm)],[c_354,c_12])).

tff(c_4,plain,(
    ! [A_2,B_3] : ~ r2_hidden(A_2,k2_zfmisc_1(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_13208,plain,(
    ! [A_1154,B_1155,C_1156,B_1157] :
      ( ~ r1_tarski(A_1154,k2_zfmisc_1(k4_tarski('#skF_4'(A_1154,B_1155,C_1156),'#skF_6'(A_1154,B_1155,C_1156)),B_1157))
      | r2_hidden(k4_tarski('#skF_7'(A_1154,B_1155,C_1156),'#skF_8'(A_1154,B_1155,C_1156)),C_1156)
      | k5_relat_1(A_1154,B_1155) = C_1156
      | ~ v1_relat_1(C_1156)
      | ~ v1_relat_1(B_1155)
      | ~ v1_relat_1(A_1154) ) ),
    inference(resolution,[status(thm)],[c_10023,c_4])).

tff(c_13211,plain,(
    ! [B_1155,C_1156] :
      ( r2_hidden(k4_tarski('#skF_7'(k1_xboole_0,B_1155,C_1156),'#skF_8'(k1_xboole_0,B_1155,C_1156)),C_1156)
      | k5_relat_1(k1_xboole_0,B_1155) = C_1156
      | ~ v1_relat_1(C_1156)
      | ~ v1_relat_1(B_1155)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_13208])).

tff(c_13215,plain,(
    ! [B_1158,C_1159] :
      ( r2_hidden(k4_tarski('#skF_7'(k1_xboole_0,B_1158,C_1159),'#skF_8'(k1_xboole_0,B_1158,C_1159)),C_1159)
      | k5_relat_1(k1_xboole_0,B_1158) = C_1159
      | ~ v1_relat_1(C_1159)
      | ~ v1_relat_1(B_1158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13211])).

tff(c_13518,plain,(
    ! [B_1169,C_1170,B_1171] :
      ( r2_hidden(k4_tarski('#skF_7'(k1_xboole_0,B_1169,C_1170),'#skF_8'(k1_xboole_0,B_1169,C_1170)),B_1171)
      | ~ r1_tarski(C_1170,B_1171)
      | k5_relat_1(k1_xboole_0,B_1169) = C_1170
      | ~ v1_relat_1(C_1170)
      | ~ v1_relat_1(B_1169) ) ),
    inference(resolution,[status(thm)],[c_13215,c_12])).

tff(c_13558,plain,(
    ! [C_1172,B_1173,B_1174] :
      ( ~ r1_tarski(C_1172,k2_zfmisc_1(k4_tarski('#skF_7'(k1_xboole_0,B_1173,C_1172),'#skF_8'(k1_xboole_0,B_1173,C_1172)),B_1174))
      | k5_relat_1(k1_xboole_0,B_1173) = C_1172
      | ~ v1_relat_1(C_1172)
      | ~ v1_relat_1(B_1173) ) ),
    inference(resolution,[status(thm)],[c_13518,c_4])).

tff(c_13562,plain,(
    ! [B_1173] :
      ( k5_relat_1(k1_xboole_0,B_1173) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_1173) ) ),
    inference(resolution,[status(thm)],[c_2,c_13558])).

tff(c_13573,plain,(
    ! [B_1179] :
      ( k5_relat_1(k1_xboole_0,B_1179) = k1_xboole_0
      | ~ v1_relat_1(B_1179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13562])).

tff(c_13588,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_13573])).

tff(c_13596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_13588])).

tff(c_13597,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_13603,plain,(
    ! [B_1180,A_1181] :
      ( v1_relat_1(B_1180)
      | ~ m1_subset_1(B_1180,k1_zfmisc_1(A_1181))
      | ~ v1_relat_1(A_1181) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13607,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_13603])).

tff(c_13608,plain,(
    ! [A_4] : ~ v1_relat_1(A_4) ),
    inference(splitLeft,[status(thm)],[c_13607])).

tff(c_13611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13608,c_38])).

tff(c_13612,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_13607])).

tff(c_14024,plain,(
    ! [A_1272,B_1273,C_1274] :
      ( r2_hidden(k4_tarski('#skF_6'(A_1272,B_1273,C_1274),'#skF_5'(A_1272,B_1273,C_1274)),B_1273)
      | r2_hidden(k4_tarski('#skF_7'(A_1272,B_1273,C_1274),'#skF_8'(A_1272,B_1273,C_1274)),C_1274)
      | k5_relat_1(A_1272,B_1273) = C_1274
      | ~ v1_relat_1(C_1274)
      | ~ v1_relat_1(B_1273)
      | ~ v1_relat_1(A_1272) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_13598,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_13777,plain,(
    ! [D_1236,A_1237,E_1238,B_1239] :
      ( r2_hidden(k4_tarski(D_1236,'#skF_3'(D_1236,A_1237,E_1238,B_1239,k5_relat_1(A_1237,B_1239))),A_1237)
      | ~ r2_hidden(k4_tarski(D_1236,E_1238),k5_relat_1(A_1237,B_1239))
      | ~ v1_relat_1(k5_relat_1(A_1237,B_1239))
      | ~ v1_relat_1(B_1239)
      | ~ v1_relat_1(A_1237) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_13790,plain,(
    ! [D_1236,E_1238] :
      ( r2_hidden(k4_tarski(D_1236,'#skF_3'(D_1236,k1_xboole_0,E_1238,'#skF_9',k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1236,E_1238),k5_relat_1(k1_xboole_0,'#skF_9'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13598,c_13777])).

tff(c_13799,plain,(
    ! [D_1240,E_1241] :
      ( r2_hidden(k4_tarski(D_1240,'#skF_3'(D_1240,k1_xboole_0,E_1241,'#skF_9',k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1240,E_1241),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13612,c_38,c_13612,c_13598,c_13598,c_13790])).

tff(c_13806,plain,(
    ! [D_1240,E_1241,B_21] :
      ( r2_hidden(k4_tarski(D_1240,'#skF_3'(D_1240,k1_xboole_0,E_1241,'#skF_9',k1_xboole_0)),B_21)
      | ~ r1_tarski(k1_xboole_0,B_21)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1240,E_1241),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13799,c_12])).

tff(c_13819,plain,(
    ! [D_1242,E_1243,B_1244] :
      ( r2_hidden(k4_tarski(D_1242,'#skF_3'(D_1242,k1_xboole_0,E_1243,'#skF_9',k1_xboole_0)),B_1244)
      | ~ r2_hidden(k4_tarski(D_1242,E_1243),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13612,c_2,c_13806])).

tff(c_13841,plain,(
    ! [D_1242,E_1243] : ~ r2_hidden(k4_tarski(D_1242,E_1243),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13819,c_4])).

tff(c_14040,plain,(
    ! [A_1272,C_1274] :
      ( r2_hidden(k4_tarski('#skF_7'(A_1272,k1_xboole_0,C_1274),'#skF_8'(A_1272,k1_xboole_0,C_1274)),C_1274)
      | k5_relat_1(A_1272,k1_xboole_0) = C_1274
      | ~ v1_relat_1(C_1274)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1272) ) ),
    inference(resolution,[status(thm)],[c_14024,c_13841])).

tff(c_14083,plain,(
    ! [A_1275,C_1276] :
      ( r2_hidden(k4_tarski('#skF_7'(A_1275,k1_xboole_0,C_1276),'#skF_8'(A_1275,k1_xboole_0,C_1276)),C_1276)
      | k5_relat_1(A_1275,k1_xboole_0) = C_1276
      | ~ v1_relat_1(C_1276)
      | ~ v1_relat_1(A_1275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13612,c_14040])).

tff(c_14099,plain,(
    ! [A_1275] :
      ( k5_relat_1(A_1275,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1275) ) ),
    inference(resolution,[status(thm)],[c_14083,c_13841])).

tff(c_14118,plain,(
    ! [A_1277] :
      ( k5_relat_1(A_1277,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_1277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13612,c_14099])).

tff(c_14124,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_14118])).

tff(c_14129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13597,c_14124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.99/5.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/5.04  
% 11.99/5.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/5.04  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 11.99/5.04  
% 11.99/5.04  %Foreground sorts:
% 11.99/5.04  
% 11.99/5.04  
% 11.99/5.04  %Background operators:
% 11.99/5.04  
% 11.99/5.04  
% 11.99/5.04  %Foreground operators:
% 11.99/5.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.99/5.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.99/5.04  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.99/5.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.99/5.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.99/5.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.99/5.04  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.99/5.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.99/5.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.99/5.04  tff('#skF_9', type, '#skF_9': $i).
% 11.99/5.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.99/5.04  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 11.99/5.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 11.99/5.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.99/5.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.99/5.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.99/5.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.99/5.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.99/5.04  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 11.99/5.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.99/5.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.99/5.04  
% 12.16/5.05  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 12.16/5.05  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 12.16/5.05  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.16/5.05  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.16/5.05  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 12.16/5.05  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 12.16/5.05  tff(f_30, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 12.16/5.05  tff(c_36, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.16/5.05  tff(c_42, plain, (k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 12.16/5.05  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.16/5.05  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.16/5.05  tff(c_43, plain, (![B_131, A_132]: (v1_relat_1(B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(A_132)) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.16/5.05  tff(c_47, plain, (![A_4]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_6, c_43])).
% 12.16/5.05  tff(c_48, plain, (![A_4]: (~v1_relat_1(A_4))), inference(splitLeft, [status(thm)], [c_47])).
% 12.16/5.05  tff(c_51, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_38])).
% 12.16/5.05  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_47])).
% 12.16/5.05  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.16/5.05  tff(c_354, plain, (![A_225, B_226, C_227]: (r2_hidden(k4_tarski('#skF_4'(A_225, B_226, C_227), '#skF_6'(A_225, B_226, C_227)), A_225) | r2_hidden(k4_tarski('#skF_7'(A_225, B_226, C_227), '#skF_8'(A_225, B_226, C_227)), C_227) | k5_relat_1(A_225, B_226)=C_227 | ~v1_relat_1(C_227) | ~v1_relat_1(B_226) | ~v1_relat_1(A_225))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.16/5.05  tff(c_12, plain, (![C_26, D_27, B_21, A_11]: (r2_hidden(k4_tarski(C_26, D_27), B_21) | ~r2_hidden(k4_tarski(C_26, D_27), A_11) | ~r1_tarski(A_11, B_21) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.16/5.05  tff(c_10023, plain, (![A_878, B_879, C_880, B_881]: (r2_hidden(k4_tarski('#skF_4'(A_878, B_879, C_880), '#skF_6'(A_878, B_879, C_880)), B_881) | ~r1_tarski(A_878, B_881) | r2_hidden(k4_tarski('#skF_7'(A_878, B_879, C_880), '#skF_8'(A_878, B_879, C_880)), C_880) | k5_relat_1(A_878, B_879)=C_880 | ~v1_relat_1(C_880) | ~v1_relat_1(B_879) | ~v1_relat_1(A_878))), inference(resolution, [status(thm)], [c_354, c_12])).
% 12.16/5.05  tff(c_4, plain, (![A_2, B_3]: (~r2_hidden(A_2, k2_zfmisc_1(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.16/5.05  tff(c_13208, plain, (![A_1154, B_1155, C_1156, B_1157]: (~r1_tarski(A_1154, k2_zfmisc_1(k4_tarski('#skF_4'(A_1154, B_1155, C_1156), '#skF_6'(A_1154, B_1155, C_1156)), B_1157)) | r2_hidden(k4_tarski('#skF_7'(A_1154, B_1155, C_1156), '#skF_8'(A_1154, B_1155, C_1156)), C_1156) | k5_relat_1(A_1154, B_1155)=C_1156 | ~v1_relat_1(C_1156) | ~v1_relat_1(B_1155) | ~v1_relat_1(A_1154))), inference(resolution, [status(thm)], [c_10023, c_4])).
% 12.16/5.05  tff(c_13211, plain, (![B_1155, C_1156]: (r2_hidden(k4_tarski('#skF_7'(k1_xboole_0, B_1155, C_1156), '#skF_8'(k1_xboole_0, B_1155, C_1156)), C_1156) | k5_relat_1(k1_xboole_0, B_1155)=C_1156 | ~v1_relat_1(C_1156) | ~v1_relat_1(B_1155) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_13208])).
% 12.16/5.05  tff(c_13215, plain, (![B_1158, C_1159]: (r2_hidden(k4_tarski('#skF_7'(k1_xboole_0, B_1158, C_1159), '#skF_8'(k1_xboole_0, B_1158, C_1159)), C_1159) | k5_relat_1(k1_xboole_0, B_1158)=C_1159 | ~v1_relat_1(C_1159) | ~v1_relat_1(B_1158))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13211])).
% 12.16/5.05  tff(c_13518, plain, (![B_1169, C_1170, B_1171]: (r2_hidden(k4_tarski('#skF_7'(k1_xboole_0, B_1169, C_1170), '#skF_8'(k1_xboole_0, B_1169, C_1170)), B_1171) | ~r1_tarski(C_1170, B_1171) | k5_relat_1(k1_xboole_0, B_1169)=C_1170 | ~v1_relat_1(C_1170) | ~v1_relat_1(B_1169))), inference(resolution, [status(thm)], [c_13215, c_12])).
% 12.16/5.05  tff(c_13558, plain, (![C_1172, B_1173, B_1174]: (~r1_tarski(C_1172, k2_zfmisc_1(k4_tarski('#skF_7'(k1_xboole_0, B_1173, C_1172), '#skF_8'(k1_xboole_0, B_1173, C_1172)), B_1174)) | k5_relat_1(k1_xboole_0, B_1173)=C_1172 | ~v1_relat_1(C_1172) | ~v1_relat_1(B_1173))), inference(resolution, [status(thm)], [c_13518, c_4])).
% 12.16/5.05  tff(c_13562, plain, (![B_1173]: (k5_relat_1(k1_xboole_0, B_1173)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_1173))), inference(resolution, [status(thm)], [c_2, c_13558])).
% 12.16/5.05  tff(c_13573, plain, (![B_1179]: (k5_relat_1(k1_xboole_0, B_1179)=k1_xboole_0 | ~v1_relat_1(B_1179))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13562])).
% 12.16/5.05  tff(c_13588, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_13573])).
% 12.16/5.05  tff(c_13596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_13588])).
% 12.16/5.05  tff(c_13597, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 12.16/5.05  tff(c_13603, plain, (![B_1180, A_1181]: (v1_relat_1(B_1180) | ~m1_subset_1(B_1180, k1_zfmisc_1(A_1181)) | ~v1_relat_1(A_1181))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.16/5.05  tff(c_13607, plain, (![A_4]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_6, c_13603])).
% 12.16/5.05  tff(c_13608, plain, (![A_4]: (~v1_relat_1(A_4))), inference(splitLeft, [status(thm)], [c_13607])).
% 12.16/5.05  tff(c_13611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13608, c_38])).
% 12.16/5.05  tff(c_13612, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_13607])).
% 12.16/5.05  tff(c_14024, plain, (![A_1272, B_1273, C_1274]: (r2_hidden(k4_tarski('#skF_6'(A_1272, B_1273, C_1274), '#skF_5'(A_1272, B_1273, C_1274)), B_1273) | r2_hidden(k4_tarski('#skF_7'(A_1272, B_1273, C_1274), '#skF_8'(A_1272, B_1273, C_1274)), C_1274) | k5_relat_1(A_1272, B_1273)=C_1274 | ~v1_relat_1(C_1274) | ~v1_relat_1(B_1273) | ~v1_relat_1(A_1272))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.16/5.05  tff(c_13598, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 12.16/5.05  tff(c_13777, plain, (![D_1236, A_1237, E_1238, B_1239]: (r2_hidden(k4_tarski(D_1236, '#skF_3'(D_1236, A_1237, E_1238, B_1239, k5_relat_1(A_1237, B_1239))), A_1237) | ~r2_hidden(k4_tarski(D_1236, E_1238), k5_relat_1(A_1237, B_1239)) | ~v1_relat_1(k5_relat_1(A_1237, B_1239)) | ~v1_relat_1(B_1239) | ~v1_relat_1(A_1237))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.16/5.05  tff(c_13790, plain, (![D_1236, E_1238]: (r2_hidden(k4_tarski(D_1236, '#skF_3'(D_1236, k1_xboole_0, E_1238, '#skF_9', k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_1236, E_1238), k5_relat_1(k1_xboole_0, '#skF_9')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13598, c_13777])).
% 12.16/5.05  tff(c_13799, plain, (![D_1240, E_1241]: (r2_hidden(k4_tarski(D_1240, '#skF_3'(D_1240, k1_xboole_0, E_1241, '#skF_9', k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_1240, E_1241), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_13612, c_38, c_13612, c_13598, c_13598, c_13790])).
% 12.16/5.05  tff(c_13806, plain, (![D_1240, E_1241, B_21]: (r2_hidden(k4_tarski(D_1240, '#skF_3'(D_1240, k1_xboole_0, E_1241, '#skF_9', k1_xboole_0)), B_21) | ~r1_tarski(k1_xboole_0, B_21) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(k4_tarski(D_1240, E_1241), k1_xboole_0))), inference(resolution, [status(thm)], [c_13799, c_12])).
% 12.16/5.05  tff(c_13819, plain, (![D_1242, E_1243, B_1244]: (r2_hidden(k4_tarski(D_1242, '#skF_3'(D_1242, k1_xboole_0, E_1243, '#skF_9', k1_xboole_0)), B_1244) | ~r2_hidden(k4_tarski(D_1242, E_1243), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_13612, c_2, c_13806])).
% 12.16/5.05  tff(c_13841, plain, (![D_1242, E_1243]: (~r2_hidden(k4_tarski(D_1242, E_1243), k1_xboole_0))), inference(resolution, [status(thm)], [c_13819, c_4])).
% 12.16/5.05  tff(c_14040, plain, (![A_1272, C_1274]: (r2_hidden(k4_tarski('#skF_7'(A_1272, k1_xboole_0, C_1274), '#skF_8'(A_1272, k1_xboole_0, C_1274)), C_1274) | k5_relat_1(A_1272, k1_xboole_0)=C_1274 | ~v1_relat_1(C_1274) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1272))), inference(resolution, [status(thm)], [c_14024, c_13841])).
% 12.16/5.05  tff(c_14083, plain, (![A_1275, C_1276]: (r2_hidden(k4_tarski('#skF_7'(A_1275, k1_xboole_0, C_1276), '#skF_8'(A_1275, k1_xboole_0, C_1276)), C_1276) | k5_relat_1(A_1275, k1_xboole_0)=C_1276 | ~v1_relat_1(C_1276) | ~v1_relat_1(A_1275))), inference(demodulation, [status(thm), theory('equality')], [c_13612, c_14040])).
% 12.16/5.05  tff(c_14099, plain, (![A_1275]: (k5_relat_1(A_1275, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1275))), inference(resolution, [status(thm)], [c_14083, c_13841])).
% 12.16/5.05  tff(c_14118, plain, (![A_1277]: (k5_relat_1(A_1277, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_1277))), inference(demodulation, [status(thm), theory('equality')], [c_13612, c_14099])).
% 12.16/5.05  tff(c_14124, plain, (k5_relat_1('#skF_9', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_14118])).
% 12.16/5.05  tff(c_14129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13597, c_14124])).
% 12.16/5.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.16/5.05  
% 12.16/5.05  Inference rules
% 12.16/5.05  ----------------------
% 12.16/5.05  #Ref     : 0
% 12.16/5.05  #Sup     : 3025
% 12.16/5.05  #Fact    : 0
% 12.16/5.05  #Define  : 0
% 12.16/5.05  #Split   : 51
% 12.16/5.05  #Chain   : 0
% 12.16/5.05  #Close   : 0
% 12.16/5.05  
% 12.16/5.05  Ordering : KBO
% 12.16/5.05  
% 12.16/5.05  Simplification rules
% 12.16/5.05  ----------------------
% 12.16/5.05  #Subsume      : 3826
% 12.16/5.05  #Demod        : 1171
% 12.16/5.05  #Tautology    : 64
% 12.16/5.05  #SimpNegUnit  : 520
% 12.16/5.05  #BackRed      : 84
% 12.16/5.05  
% 12.16/5.05  #Partial instantiations: 0
% 12.16/5.05  #Strategies tried      : 1
% 12.16/5.05  
% 12.16/5.05  Timing (in seconds)
% 12.16/5.05  ----------------------
% 12.16/5.06  Preprocessing        : 0.31
% 12.16/5.06  Parsing              : 0.17
% 12.16/5.06  CNF conversion       : 0.03
% 12.16/5.06  Main loop            : 3.97
% 12.16/5.06  Inferencing          : 0.80
% 12.16/5.06  Reduction            : 0.56
% 12.16/5.06  Demodulation         : 0.36
% 12.16/5.06  BG Simplification    : 0.09
% 12.16/5.06  Subsumption          : 2.30
% 12.16/5.06  Abstraction          : 0.16
% 12.16/5.06  MUC search           : 0.00
% 12.16/5.06  Cooper               : 0.00
% 12.16/5.06  Total                : 4.31
% 12.16/5.06  Index Insertion      : 0.00
% 12.16/5.06  Index Deletion       : 0.00
% 12.16/5.06  Index Matching       : 0.00
% 12.16/5.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
