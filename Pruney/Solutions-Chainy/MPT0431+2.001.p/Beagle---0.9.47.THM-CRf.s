%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 19.78s
% Output     : CNFRefutation 19.88s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 264 expanded)
%              Number of leaves         :   23 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 732 expanded)
%              Number of equality atoms :   20 ( 140 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_46,plain,(
    v3_setfam_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_133,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden(A_53,B_54)
      | ~ v3_setfam_1(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ v3_setfam_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_133])).

tff(c_147,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_140])).

tff(c_42,plain,(
    v3_setfam_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_143,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ v3_setfam_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_133])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_143])).

tff(c_188,plain,(
    ! [A_60,B_61,C_62] :
      ( k4_subset_1(A_60,B_61,C_62) = k2_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_213,plain,(
    ! [B_72] :
      ( k4_subset_1(k1_zfmisc_1('#skF_4'),B_72,'#skF_6') = k2_xboole_0(B_72,'#skF_6')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_188])).

tff(c_225,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_4'),'#skF_5','#skF_6') = k2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_213])).

tff(c_38,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_4'),'#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_227,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_38])).

tff(c_49,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_49])).

tff(c_647,plain,(
    ! [A_137,B_138,C_139] :
      ( r2_hidden('#skF_2'(A_137,B_138,C_139),B_138)
      | r2_hidden('#skF_2'(A_137,B_138,C_139),A_137)
      | r2_hidden('#skF_3'(A_137,B_138,C_139),C_139)
      | k2_xboole_0(A_137,B_138) = C_139 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_699,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_2'(A_137,B_138,A_137),B_138)
      | r2_hidden('#skF_3'(A_137,B_138,A_137),A_137)
      | k2_xboole_0(A_137,B_138) = A_137 ) ),
    inference(resolution,[status(thm)],[c_647,c_22])).

tff(c_898,plain,(
    ! [A_165,B_166,C_167] :
      ( r2_hidden('#skF_2'(A_165,B_166,C_167),B_166)
      | r2_hidden('#skF_2'(A_165,B_166,C_167),A_165)
      | ~ r2_hidden('#skF_3'(A_165,B_166,C_167),A_165)
      | k2_xboole_0(A_165,B_166) = C_167 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6072,plain,(
    ! [A_432,B_433] :
      ( r2_hidden('#skF_2'(A_432,B_433,A_432),B_433)
      | ~ r2_hidden('#skF_3'(A_432,B_433,A_432),A_432)
      | k2_xboole_0(A_432,B_433) = A_432 ) ),
    inference(resolution,[status(thm)],[c_898,c_18])).

tff(c_6134,plain,(
    ! [A_434,B_435] :
      ( r2_hidden('#skF_2'(A_434,B_435,A_434),B_435)
      | k2_xboole_0(A_434,B_435) = A_434 ) ),
    inference(resolution,[status(thm)],[c_699,c_6072])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6243,plain,(
    ! [A_437,B_438,B_439] :
      ( r2_hidden('#skF_2'(A_437,B_438,A_437),B_439)
      | ~ r1_tarski(B_438,B_439)
      | k2_xboole_0(A_437,B_438) = A_437 ) ),
    inference(resolution,[status(thm)],[c_6134,c_2])).

tff(c_6549,plain,(
    ! [B_449,B_450] :
      ( r2_hidden('#skF_3'(B_449,B_450,B_449),B_449)
      | ~ r1_tarski(B_450,B_449)
      | k2_xboole_0(B_449,B_450) = B_449 ) ),
    inference(resolution,[status(thm)],[c_6243,c_22])).

tff(c_6289,plain,(
    ! [B_439,B_438] :
      ( ~ r2_hidden('#skF_3'(B_439,B_438,B_439),B_439)
      | ~ r1_tarski(B_438,B_439)
      | k2_xboole_0(B_439,B_438) = B_439 ) ),
    inference(resolution,[status(thm)],[c_6243,c_18])).

tff(c_6605,plain,(
    ! [B_451,B_452] :
      ( ~ r1_tarski(B_451,B_452)
      | k2_xboole_0(B_452,B_451) = B_452 ) ),
    inference(resolution,[status(thm)],[c_6549,c_6289])).

tff(c_6713,plain,(
    k2_xboole_0(k1_zfmisc_1('#skF_4'),'#skF_6') = k1_zfmisc_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_6605])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [D_48,B_49,A_50] :
      ( r2_hidden(D_48,B_49)
      | r2_hidden(D_48,A_50)
      | ~ r2_hidden(D_48,k2_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8216,plain,(
    ! [A_464,B_465,B_466] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_464,B_465),B_466),B_465)
      | r2_hidden('#skF_1'(k2_xboole_0(A_464,B_465),B_466),A_464)
      | r1_tarski(k2_xboole_0(A_464,B_465),B_466) ) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_77,plain,(
    ! [D_39,A_40,B_41] :
      ( ~ r2_hidden(D_39,A_40)
      | r2_hidden(D_39,k2_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_1,A_40,B_41] :
      ( r1_tarski(A_1,k2_xboole_0(A_40,B_41))
      | ~ r2_hidden('#skF_1'(A_1,k2_xboole_0(A_40,B_41)),A_40) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_58463,plain,(
    ! [A_1206,B_1207,B_1208] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_1206,B_1207),k2_xboole_0(A_1206,B_1208)),B_1207)
      | r1_tarski(k2_xboole_0(A_1206,B_1207),k2_xboole_0(A_1206,B_1208)) ) ),
    inference(resolution,[status(thm)],[c_8216,c_82])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [D_36,B_37,A_38] :
      ( ~ r2_hidden(D_36,B_37)
      | r2_hidden(D_36,k2_xboole_0(A_38,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_267,plain,(
    ! [A_83,A_84,B_85] :
      ( r1_tarski(A_83,k2_xboole_0(A_84,B_85))
      | ~ r2_hidden('#skF_1'(A_83,k2_xboole_0(A_84,B_85)),B_85) ) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_286,plain,(
    ! [A_83,A_84,A_6,B_7] :
      ( r1_tarski(A_83,k2_xboole_0(A_84,k2_xboole_0(A_6,B_7)))
      | ~ r2_hidden('#skF_1'(A_83,k2_xboole_0(A_84,k2_xboole_0(A_6,B_7))),B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_267])).

tff(c_58684,plain,(
    ! [A_1209,B_1210,A_1211] : r1_tarski(k2_xboole_0(A_1209,B_1210),k2_xboole_0(A_1209,k2_xboole_0(A_1211,B_1210))) ),
    inference(resolution,[status(thm)],[c_58463,c_286])).

tff(c_59275,plain,(
    ! [A_1213] : r1_tarski(k2_xboole_0(A_1213,'#skF_6'),k2_xboole_0(A_1213,k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6713,c_58684])).

tff(c_43122,plain,(
    ! [A_1087,B_1088] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_1087,B_1088),B_1088),A_1087)
      | r1_tarski(k2_xboole_0(A_1087,B_1088),B_1088) ) ),
    inference(resolution,[status(thm)],[c_8216,c_4])).

tff(c_56,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_6714,plain,(
    k2_xboole_0(k1_zfmisc_1('#skF_4'),'#skF_5') = k1_zfmisc_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6605])).

tff(c_76,plain,(
    ! [A_1,A_38,B_37] :
      ( r1_tarski(A_1,k2_xboole_0(A_38,B_37))
      | ~ r2_hidden('#skF_1'(A_1,k2_xboole_0(A_38,B_37)),B_37) ) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_7127,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k2_xboole_0(k1_zfmisc_1('#skF_4'),'#skF_5'))
      | ~ r2_hidden('#skF_1'(A_1,k1_zfmisc_1('#skF_4')),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6714,c_76])).

tff(c_7159,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_1,k1_zfmisc_1('#skF_4')),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6714,c_7127])).

tff(c_43219,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k1_zfmisc_1('#skF_4')),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_43122,c_7159])).

tff(c_6589,plain,(
    ! [B_450,B_449] :
      ( ~ r1_tarski(B_450,B_449)
      | k2_xboole_0(B_449,B_450) = B_449 ) ),
    inference(resolution,[status(thm)],[c_6549,c_6289])).

tff(c_43423,plain,(
    k2_xboole_0(k1_zfmisc_1('#skF_4'),k2_xboole_0('#skF_5',k1_zfmisc_1('#skF_4'))) = k1_zfmisc_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43219,c_6589])).

tff(c_83,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_1,B_2,B_43] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_43)
      | ~ r1_tarski(A_1,B_43)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_284,plain,(
    ! [A_1,B_43,A_84] :
      ( ~ r1_tarski(A_1,B_43)
      | r1_tarski(A_1,k2_xboole_0(A_84,B_43)) ) ),
    inference(resolution,[status(thm)],[c_92,c_267])).

tff(c_45364,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,k2_xboole_0('#skF_5',k1_zfmisc_1('#skF_4')))
      | r1_tarski(A_1,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43423,c_284])).

tff(c_59414,plain,(
    r1_tarski(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59275,c_45364])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,(
    ! [B_51,A_52] :
      ( v3_setfam_1(B_51,A_52)
      | r2_hidden(A_52,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_128,plain,(
    ! [A_21,A_52] :
      ( v3_setfam_1(A_21,A_52)
      | r2_hidden(A_52,A_21)
      | ~ r1_tarski(A_21,k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_36,c_117])).

tff(c_59512,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_5','#skF_6'),'#skF_4')
    | r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_59414,c_128])).

tff(c_59542,plain,(
    r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_59512])).

tff(c_8,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59574,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_59542,c_8])).

tff(c_59596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_150,c_59574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:59:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.78/10.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.88/10.81  
% 19.88/10.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.88/10.81  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 19.88/10.81  
% 19.88/10.81  %Foreground sorts:
% 19.88/10.81  
% 19.88/10.81  
% 19.88/10.81  %Background operators:
% 19.88/10.81  
% 19.88/10.81  
% 19.88/10.81  %Foreground operators:
% 19.88/10.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.88/10.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.88/10.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.88/10.81  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 19.88/10.81  tff('#skF_5', type, '#skF_5': $i).
% 19.88/10.81  tff('#skF_6', type, '#skF_6': $i).
% 19.88/10.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 19.88/10.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.88/10.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.88/10.81  tff('#skF_4', type, '#skF_4': $i).
% 19.88/10.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 19.88/10.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.88/10.81  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 19.88/10.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.88/10.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.88/10.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.88/10.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.88/10.81  
% 19.88/10.83  tff(f_81, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 19.88/10.83  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 19.88/10.83  tff(f_54, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 19.88/10.83  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 19.88/10.83  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 19.88/10.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 19.88/10.83  tff(c_46, plain, (v3_setfam_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.88/10.83  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.88/10.83  tff(c_133, plain, (![A_53, B_54]: (~r2_hidden(A_53, B_54) | ~v3_setfam_1(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.88/10.83  tff(c_140, plain, (~r2_hidden('#skF_4', '#skF_5') | ~v3_setfam_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_133])).
% 19.88/10.83  tff(c_147, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_140])).
% 19.88/10.83  tff(c_42, plain, (v3_setfam_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.88/10.83  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.88/10.83  tff(c_143, plain, (~r2_hidden('#skF_4', '#skF_6') | ~v3_setfam_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_133])).
% 19.88/10.83  tff(c_150, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_143])).
% 19.88/10.83  tff(c_188, plain, (![A_60, B_61, C_62]: (k4_subset_1(A_60, B_61, C_62)=k2_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.88/10.83  tff(c_213, plain, (![B_72]: (k4_subset_1(k1_zfmisc_1('#skF_4'), B_72, '#skF_6')=k2_xboole_0(B_72, '#skF_6') | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(resolution, [status(thm)], [c_40, c_188])).
% 19.88/10.83  tff(c_225, plain, (k4_subset_1(k1_zfmisc_1('#skF_4'), '#skF_5', '#skF_6')=k2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_213])).
% 19.88/10.83  tff(c_38, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_4'), '#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.88/10.83  tff(c_227, plain, (~v3_setfam_1(k2_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_38])).
% 19.88/10.83  tff(c_49, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.88/10.83  tff(c_57, plain, (r1_tarski('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_49])).
% 19.88/10.83  tff(c_647, plain, (![A_137, B_138, C_139]: (r2_hidden('#skF_2'(A_137, B_138, C_139), B_138) | r2_hidden('#skF_2'(A_137, B_138, C_139), A_137) | r2_hidden('#skF_3'(A_137, B_138, C_139), C_139) | k2_xboole_0(A_137, B_138)=C_139)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_699, plain, (![A_137, B_138]: (r2_hidden('#skF_2'(A_137, B_138, A_137), B_138) | r2_hidden('#skF_3'(A_137, B_138, A_137), A_137) | k2_xboole_0(A_137, B_138)=A_137)), inference(resolution, [status(thm)], [c_647, c_22])).
% 19.88/10.83  tff(c_898, plain, (![A_165, B_166, C_167]: (r2_hidden('#skF_2'(A_165, B_166, C_167), B_166) | r2_hidden('#skF_2'(A_165, B_166, C_167), A_165) | ~r2_hidden('#skF_3'(A_165, B_166, C_167), A_165) | k2_xboole_0(A_165, B_166)=C_167)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_18, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_6072, plain, (![A_432, B_433]: (r2_hidden('#skF_2'(A_432, B_433, A_432), B_433) | ~r2_hidden('#skF_3'(A_432, B_433, A_432), A_432) | k2_xboole_0(A_432, B_433)=A_432)), inference(resolution, [status(thm)], [c_898, c_18])).
% 19.88/10.83  tff(c_6134, plain, (![A_434, B_435]: (r2_hidden('#skF_2'(A_434, B_435, A_434), B_435) | k2_xboole_0(A_434, B_435)=A_434)), inference(resolution, [status(thm)], [c_699, c_6072])).
% 19.88/10.83  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.88/10.83  tff(c_6243, plain, (![A_437, B_438, B_439]: (r2_hidden('#skF_2'(A_437, B_438, A_437), B_439) | ~r1_tarski(B_438, B_439) | k2_xboole_0(A_437, B_438)=A_437)), inference(resolution, [status(thm)], [c_6134, c_2])).
% 19.88/10.83  tff(c_6549, plain, (![B_449, B_450]: (r2_hidden('#skF_3'(B_449, B_450, B_449), B_449) | ~r1_tarski(B_450, B_449) | k2_xboole_0(B_449, B_450)=B_449)), inference(resolution, [status(thm)], [c_6243, c_22])).
% 19.88/10.83  tff(c_6289, plain, (![B_439, B_438]: (~r2_hidden('#skF_3'(B_439, B_438, B_439), B_439) | ~r1_tarski(B_438, B_439) | k2_xboole_0(B_439, B_438)=B_439)), inference(resolution, [status(thm)], [c_6243, c_18])).
% 19.88/10.83  tff(c_6605, plain, (![B_451, B_452]: (~r1_tarski(B_451, B_452) | k2_xboole_0(B_452, B_451)=B_452)), inference(resolution, [status(thm)], [c_6549, c_6289])).
% 19.88/10.83  tff(c_6713, plain, (k2_xboole_0(k1_zfmisc_1('#skF_4'), '#skF_6')=k1_zfmisc_1('#skF_4')), inference(resolution, [status(thm)], [c_57, c_6605])).
% 19.88/10.83  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.88/10.83  tff(c_103, plain, (![D_48, B_49, A_50]: (r2_hidden(D_48, B_49) | r2_hidden(D_48, A_50) | ~r2_hidden(D_48, k2_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_8216, plain, (![A_464, B_465, B_466]: (r2_hidden('#skF_1'(k2_xboole_0(A_464, B_465), B_466), B_465) | r2_hidden('#skF_1'(k2_xboole_0(A_464, B_465), B_466), A_464) | r1_tarski(k2_xboole_0(A_464, B_465), B_466))), inference(resolution, [status(thm)], [c_6, c_103])).
% 19.88/10.83  tff(c_77, plain, (![D_39, A_40, B_41]: (~r2_hidden(D_39, A_40) | r2_hidden(D_39, k2_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.88/10.83  tff(c_82, plain, (![A_1, A_40, B_41]: (r1_tarski(A_1, k2_xboole_0(A_40, B_41)) | ~r2_hidden('#skF_1'(A_1, k2_xboole_0(A_40, B_41)), A_40))), inference(resolution, [status(thm)], [c_77, c_4])).
% 19.88/10.83  tff(c_58463, plain, (![A_1206, B_1207, B_1208]: (r2_hidden('#skF_1'(k2_xboole_0(A_1206, B_1207), k2_xboole_0(A_1206, B_1208)), B_1207) | r1_tarski(k2_xboole_0(A_1206, B_1207), k2_xboole_0(A_1206, B_1208)))), inference(resolution, [status(thm)], [c_8216, c_82])).
% 19.88/10.83  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_71, plain, (![D_36, B_37, A_38]: (~r2_hidden(D_36, B_37) | r2_hidden(D_36, k2_xboole_0(A_38, B_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_267, plain, (![A_83, A_84, B_85]: (r1_tarski(A_83, k2_xboole_0(A_84, B_85)) | ~r2_hidden('#skF_1'(A_83, k2_xboole_0(A_84, B_85)), B_85))), inference(resolution, [status(thm)], [c_71, c_4])).
% 19.88/10.83  tff(c_286, plain, (![A_83, A_84, A_6, B_7]: (r1_tarski(A_83, k2_xboole_0(A_84, k2_xboole_0(A_6, B_7))) | ~r2_hidden('#skF_1'(A_83, k2_xboole_0(A_84, k2_xboole_0(A_6, B_7))), B_7))), inference(resolution, [status(thm)], [c_10, c_267])).
% 19.88/10.83  tff(c_58684, plain, (![A_1209, B_1210, A_1211]: (r1_tarski(k2_xboole_0(A_1209, B_1210), k2_xboole_0(A_1209, k2_xboole_0(A_1211, B_1210))))), inference(resolution, [status(thm)], [c_58463, c_286])).
% 19.88/10.83  tff(c_59275, plain, (![A_1213]: (r1_tarski(k2_xboole_0(A_1213, '#skF_6'), k2_xboole_0(A_1213, k1_zfmisc_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_6713, c_58684])).
% 19.88/10.83  tff(c_43122, plain, (![A_1087, B_1088]: (r2_hidden('#skF_1'(k2_xboole_0(A_1087, B_1088), B_1088), A_1087) | r1_tarski(k2_xboole_0(A_1087, B_1088), B_1088))), inference(resolution, [status(thm)], [c_8216, c_4])).
% 19.88/10.83  tff(c_56, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_49])).
% 19.88/10.83  tff(c_6714, plain, (k2_xboole_0(k1_zfmisc_1('#skF_4'), '#skF_5')=k1_zfmisc_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6605])).
% 19.88/10.83  tff(c_76, plain, (![A_1, A_38, B_37]: (r1_tarski(A_1, k2_xboole_0(A_38, B_37)) | ~r2_hidden('#skF_1'(A_1, k2_xboole_0(A_38, B_37)), B_37))), inference(resolution, [status(thm)], [c_71, c_4])).
% 19.88/10.83  tff(c_7127, plain, (![A_1]: (r1_tarski(A_1, k2_xboole_0(k1_zfmisc_1('#skF_4'), '#skF_5')) | ~r2_hidden('#skF_1'(A_1, k1_zfmisc_1('#skF_4')), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6714, c_76])).
% 19.88/10.83  tff(c_7159, plain, (![A_1]: (r1_tarski(A_1, k1_zfmisc_1('#skF_4')) | ~r2_hidden('#skF_1'(A_1, k1_zfmisc_1('#skF_4')), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6714, c_7127])).
% 19.88/10.83  tff(c_43219, plain, (r1_tarski(k2_xboole_0('#skF_5', k1_zfmisc_1('#skF_4')), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_43122, c_7159])).
% 19.88/10.83  tff(c_6589, plain, (![B_450, B_449]: (~r1_tarski(B_450, B_449) | k2_xboole_0(B_449, B_450)=B_449)), inference(resolution, [status(thm)], [c_6549, c_6289])).
% 19.88/10.83  tff(c_43423, plain, (k2_xboole_0(k1_zfmisc_1('#skF_4'), k2_xboole_0('#skF_5', k1_zfmisc_1('#skF_4')))=k1_zfmisc_1('#skF_4')), inference(resolution, [status(thm)], [c_43219, c_6589])).
% 19.88/10.83  tff(c_83, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.88/10.83  tff(c_92, plain, (![A_1, B_2, B_43]: (r2_hidden('#skF_1'(A_1, B_2), B_43) | ~r1_tarski(A_1, B_43) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_83])).
% 19.88/10.83  tff(c_284, plain, (![A_1, B_43, A_84]: (~r1_tarski(A_1, B_43) | r1_tarski(A_1, k2_xboole_0(A_84, B_43)))), inference(resolution, [status(thm)], [c_92, c_267])).
% 19.88/10.83  tff(c_45364, plain, (![A_1]: (~r1_tarski(A_1, k2_xboole_0('#skF_5', k1_zfmisc_1('#skF_4'))) | r1_tarski(A_1, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_43423, c_284])).
% 19.88/10.83  tff(c_59414, plain, (r1_tarski(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_59275, c_45364])).
% 19.88/10.83  tff(c_36, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.88/10.83  tff(c_117, plain, (![B_51, A_52]: (v3_setfam_1(B_51, A_52) | r2_hidden(A_52, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.88/10.83  tff(c_128, plain, (![A_21, A_52]: (v3_setfam_1(A_21, A_52) | r2_hidden(A_52, A_21) | ~r1_tarski(A_21, k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_36, c_117])).
% 19.88/10.83  tff(c_59512, plain, (v3_setfam_1(k2_xboole_0('#skF_5', '#skF_6'), '#skF_4') | r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_59414, c_128])).
% 19.88/10.83  tff(c_59542, plain, (r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_227, c_59512])).
% 19.88/10.83  tff(c_8, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.88/10.83  tff(c_59574, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_59542, c_8])).
% 19.88/10.83  tff(c_59596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_150, c_59574])).
% 19.88/10.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.88/10.83  
% 19.88/10.83  Inference rules
% 19.88/10.83  ----------------------
% 19.88/10.83  #Ref     : 0
% 19.88/10.83  #Sup     : 15239
% 19.88/10.83  #Fact    : 56
% 19.88/10.83  #Define  : 0
% 19.88/10.83  #Split   : 2
% 19.88/10.83  #Chain   : 0
% 19.88/10.83  #Close   : 0
% 19.88/10.83  
% 19.88/10.83  Ordering : KBO
% 19.88/10.83  
% 19.88/10.83  Simplification rules
% 19.88/10.83  ----------------------
% 19.88/10.83  #Subsume      : 2787
% 19.88/10.83  #Demod        : 6918
% 19.88/10.83  #Tautology    : 5079
% 19.88/10.83  #SimpNegUnit  : 4
% 19.88/10.83  #BackRed      : 8
% 19.88/10.83  
% 19.88/10.83  #Partial instantiations: 0
% 19.88/10.83  #Strategies tried      : 1
% 19.88/10.83  
% 19.88/10.83  Timing (in seconds)
% 19.88/10.83  ----------------------
% 19.88/10.83  Preprocessing        : 0.34
% 19.88/10.83  Parsing              : 0.17
% 19.88/10.83  CNF conversion       : 0.03
% 19.88/10.83  Main loop            : 9.77
% 19.88/10.83  Inferencing          : 1.51
% 19.88/10.83  Reduction            : 3.42
% 19.88/10.83  Demodulation         : 2.81
% 19.88/10.83  BG Simplification    : 0.18
% 19.88/10.83  Subsumption          : 4.12
% 19.88/10.83  Abstraction          : 0.27
% 19.88/10.83  MUC search           : 0.00
% 19.88/10.83  Cooper               : 0.00
% 19.88/10.83  Total                : 10.14
% 19.88/10.83  Index Insertion      : 0.00
% 19.88/10.83  Index Deletion       : 0.00
% 19.88/10.83  Index Matching       : 0.00
% 19.88/10.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
