%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 12.38s
% Output     : CNFRefutation 12.38s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 252 expanded)
%              Number of leaves         :   21 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 695 expanded)
%              Number of equality atoms :   31 ( 164 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_246,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r2_hidden('#skF_1'(A_67,B_68,C_69),C_69)
      | r2_hidden('#skF_2'(A_67,B_68,C_69),C_69)
      | k3_xboole_0(A_67,B_68) = C_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_260,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_246])).

tff(c_98,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_1'(A_51,B_52,C_53),B_52)
      | r2_hidden('#skF_2'(A_51,B_52,C_53),C_53)
      | k3_xboole_0(A_51,B_52) = C_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1428,plain,(
    ! [A_155,B_156,A_157,B_158] :
      ( r2_hidden('#skF_2'(A_155,B_156,k3_xboole_0(A_157,B_158)),B_158)
      | r2_hidden('#skF_1'(A_155,B_156,k3_xboole_0(A_157,B_158)),B_156)
      | k3_xboole_0(A_157,B_158) = k3_xboole_0(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1477,plain,(
    ! [B_158,B_156,A_157] :
      ( ~ r2_hidden('#skF_2'(B_158,B_156,k3_xboole_0(A_157,B_158)),B_156)
      | r2_hidden('#skF_1'(B_158,B_156,k3_xboole_0(A_157,B_158)),B_156)
      | k3_xboole_0(B_158,B_156) = k3_xboole_0(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_1428,c_10])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1484,plain,(
    ! [B_2,A_1,A_155,A_157,B_158] :
      ( r2_hidden('#skF_1'(A_155,k3_xboole_0(A_1,B_2),k3_xboole_0(A_157,B_158)),A_1)
      | r2_hidden('#skF_2'(A_155,k3_xboole_0(A_1,B_2),k3_xboole_0(A_157,B_158)),B_158)
      | k3_xboole_0(A_157,B_158) = k3_xboole_0(A_155,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_1428,c_6])).

tff(c_225,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden('#skF_1'(A_64,B_65,C_66),A_64)
      | r2_hidden('#skF_2'(A_64,B_65,C_66),C_66)
      | k3_xboole_0(A_64,B_65) = C_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_244,plain,(
    ! [A_64,B_65,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_64,B_65,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_64,B_65,k3_xboole_0(A_1,B_2)),A_64)
      | k3_xboole_0(A_64,B_65) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_225,c_4])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1649,plain,(
    ! [A_172,B_173,A_174,B_175] :
      ( r2_hidden('#skF_2'(A_172,B_173,k3_xboole_0(A_174,B_175)),k3_xboole_0(A_174,B_175))
      | k3_xboole_0(A_174,B_175) = k3_xboole_0(A_172,B_173)
      | ~ r2_hidden('#skF_1'(A_172,B_173,k3_xboole_0(A_174,B_175)),B_175)
      | ~ r2_hidden('#skF_1'(A_172,B_173,k3_xboole_0(A_174,B_175)),A_174) ) ),
    inference(resolution,[status(thm)],[c_2,c_246])).

tff(c_10080,plain,(
    ! [A_658,B_659,A_660,B_661] :
      ( r2_hidden('#skF_2'(A_658,B_659,k3_xboole_0(A_660,B_661)),B_661)
      | k3_xboole_0(A_660,B_661) = k3_xboole_0(A_658,B_659)
      | ~ r2_hidden('#skF_1'(A_658,B_659,k3_xboole_0(A_660,B_661)),B_661)
      | ~ r2_hidden('#skF_1'(A_658,B_659,k3_xboole_0(A_660,B_661)),A_660) ) ),
    inference(resolution,[status(thm)],[c_1649,c_4])).

tff(c_10685,plain,(
    ! [A_681,B_682,A_683] :
      ( ~ r2_hidden('#skF_1'(A_681,B_682,k3_xboole_0(A_683,A_681)),A_683)
      | r2_hidden('#skF_2'(A_681,B_682,k3_xboole_0(A_683,A_681)),A_681)
      | k3_xboole_0(A_683,A_681) = k3_xboole_0(A_681,B_682) ) ),
    inference(resolution,[status(thm)],[c_244,c_10080])).

tff(c_10799,plain,(
    ! [B_158,A_1,B_2] :
      ( r2_hidden('#skF_2'(B_158,k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_158)),B_158)
      | k3_xboole_0(B_158,k3_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_158) ) ),
    inference(resolution,[status(thm)],[c_1484,c_10685])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_342,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_1'(A_76,B_77,C_78),A_76)
      | ~ r2_hidden('#skF_2'(A_76,B_77,C_78),B_77)
      | ~ r2_hidden('#skF_2'(A_76,B_77,C_78),A_76)
      | k3_xboole_0(A_76,B_77) = C_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_357,plain,(
    ! [A_1,C_3] :
      ( ~ r2_hidden('#skF_2'(A_1,C_3,C_3),A_1)
      | r2_hidden('#skF_1'(A_1,C_3,C_3),A_1)
      | k3_xboole_0(A_1,C_3) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_342])).

tff(c_375,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r2_hidden('#skF_1'(A_81,B_82,C_83),C_83)
      | ~ r2_hidden('#skF_2'(A_81,B_82,C_83),B_82)
      | ~ r2_hidden('#skF_2'(A_81,B_82,C_83),A_81)
      | k3_xboole_0(A_81,B_82) = C_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_392,plain,(
    ! [A_84] :
      ( ~ r2_hidden('#skF_2'(A_84,A_84,A_84),A_84)
      | k3_xboole_0(A_84,A_84) = A_84 ) ),
    inference(resolution,[status(thm)],[c_357,c_375])).

tff(c_409,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_260,c_392])).

tff(c_261,plain,(
    ! [A_67,B_68,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_67,B_68,k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2))
      | k3_xboole_0(A_67,B_68) = k3_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_67,B_68,k3_xboole_0(A_1,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_67,B_68,k3_xboole_0(A_1,B_2)),A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_246])).

tff(c_2383,plain,(
    ! [A_229,B_230,A_231,B_232] :
      ( ~ r2_hidden('#skF_2'(A_229,B_230,k3_xboole_0(A_231,B_232)),B_230)
      | ~ r2_hidden('#skF_2'(A_229,B_230,k3_xboole_0(A_231,B_232)),A_229)
      | k3_xboole_0(A_231,B_232) = k3_xboole_0(A_229,B_230)
      | ~ r2_hidden('#skF_1'(A_229,B_230,k3_xboole_0(A_231,B_232)),B_232)
      | ~ r2_hidden('#skF_1'(A_229,B_230,k3_xboole_0(A_231,B_232)),A_231) ) ),
    inference(resolution,[status(thm)],[c_2,c_375])).

tff(c_13075,plain,(
    ! [A_783,A_784,B_785] :
      ( ~ r2_hidden('#skF_2'(A_783,k3_xboole_0(A_784,B_785),k3_xboole_0(A_784,B_785)),A_783)
      | k3_xboole_0(A_783,k3_xboole_0(A_784,B_785)) = k3_xboole_0(A_784,B_785)
      | ~ r2_hidden('#skF_1'(A_783,k3_xboole_0(A_784,B_785),k3_xboole_0(A_784,B_785)),B_785)
      | ~ r2_hidden('#skF_1'(A_783,k3_xboole_0(A_784,B_785),k3_xboole_0(A_784,B_785)),A_784) ) ),
    inference(resolution,[status(thm)],[c_261,c_2383])).

tff(c_13191,plain,(
    ! [A_783,B_2] :
      ( ~ r2_hidden('#skF_2'(A_783,B_2,k3_xboole_0(B_2,B_2)),A_783)
      | k3_xboole_0(A_783,k3_xboole_0(B_2,B_2)) = k3_xboole_0(B_2,B_2)
      | ~ r2_hidden('#skF_1'(A_783,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_783,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_13075])).

tff(c_13262,plain,(
    ! [A_786,B_787] :
      ( ~ r2_hidden('#skF_2'(A_786,B_787,B_787),A_786)
      | k3_xboole_0(A_786,B_787) = B_787
      | ~ r2_hidden('#skF_1'(A_786,B_787,B_787),B_787)
      | ~ r2_hidden('#skF_1'(A_786,B_787,B_787),B_787) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_409,c_409,c_409,c_409,c_409,c_409,c_13191])).

tff(c_13454,plain,(
    ! [B_788,A_789] :
      ( ~ r2_hidden('#skF_1'(B_788,k3_xboole_0(A_789,B_788),k3_xboole_0(A_789,B_788)),k3_xboole_0(A_789,B_788))
      | k3_xboole_0(B_788,k3_xboole_0(A_789,B_788)) = k3_xboole_0(A_789,B_788) ) ),
    inference(resolution,[status(thm)],[c_10799,c_13262])).

tff(c_13668,plain,(
    ! [B_796,A_797] :
      ( ~ r2_hidden('#skF_2'(B_796,k3_xboole_0(A_797,B_796),k3_xboole_0(A_797,B_796)),k3_xboole_0(A_797,B_796))
      | k3_xboole_0(B_796,k3_xboole_0(A_797,B_796)) = k3_xboole_0(A_797,B_796) ) ),
    inference(resolution,[status(thm)],[c_1477,c_13454])).

tff(c_13784,plain,(
    ! [A_798,A_799] : k3_xboole_0(A_798,k3_xboole_0(A_799,A_798)) = k3_xboole_0(A_799,A_798) ),
    inference(resolution,[status(thm)],[c_260,c_13668])).

tff(c_40,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_34,B_35] : r1_tarski(k3_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_22])).

tff(c_15228,plain,(
    ! [A_799,A_798] : r1_tarski(k3_xboole_0(A_799,A_798),A_798) ),
    inference(superposition,[status(thm),theory(equality)],[c_13784,c_52])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k4_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k3_xboole_0(A_34,B_35))
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_208,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(k5_relat_1(C_61,A_62),k5_relat_1(C_61,B_63))
      | ~ r1_tarski(A_62,B_63)
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_192,plain,(
    ! [C_58,A_59,B_60] :
      ( r1_tarski(k5_relat_1(C_58,A_59),k5_relat_1(C_58,B_60))
      | ~ r1_tarski(A_59,B_60)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(A_45,k3_xboole_0(B_46,C_47))
      | ~ r1_tarski(A_45,C_47)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_88,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_30])).

tff(c_191,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_195,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_192,c_191])).

tff(c_198,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_52,c_195])).

tff(c_201,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_201])).

tff(c_206,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_211,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_208,c_206])).

tff(c_214,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_211])).

tff(c_215,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_218,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_223,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_15697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15228,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:43:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.38/4.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.38/4.53  
% 12.38/4.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.38/4.53  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 12.38/4.53  
% 12.38/4.53  %Foreground sorts:
% 12.38/4.53  
% 12.38/4.53  
% 12.38/4.53  %Background operators:
% 12.38/4.53  
% 12.38/4.53  
% 12.38/4.53  %Foreground operators:
% 12.38/4.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.38/4.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.38/4.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.38/4.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.38/4.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.38/4.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.38/4.53  tff('#skF_5', type, '#skF_5': $i).
% 12.38/4.53  tff('#skF_3', type, '#skF_3': $i).
% 12.38/4.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.38/4.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.38/4.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.38/4.53  tff('#skF_4', type, '#skF_4': $i).
% 12.38/4.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.38/4.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.38/4.53  
% 12.38/4.55  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 12.38/4.55  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.38/4.55  tff(f_42, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.38/4.55  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 12.38/4.55  tff(f_48, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 12.38/4.55  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 12.38/4.55  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 12.38/4.55  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_246, plain, (![A_67, B_68, C_69]: (~r2_hidden('#skF_1'(A_67, B_68, C_69), C_69) | r2_hidden('#skF_2'(A_67, B_68, C_69), C_69) | k3_xboole_0(A_67, B_68)=C_69)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_260, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_246])).
% 12.38/4.55  tff(c_98, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_1'(A_51, B_52, C_53), B_52) | r2_hidden('#skF_2'(A_51, B_52, C_53), C_53) | k3_xboole_0(A_51, B_52)=C_53)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_1428, plain, (![A_155, B_156, A_157, B_158]: (r2_hidden('#skF_2'(A_155, B_156, k3_xboole_0(A_157, B_158)), B_158) | r2_hidden('#skF_1'(A_155, B_156, k3_xboole_0(A_157, B_158)), B_156) | k3_xboole_0(A_157, B_158)=k3_xboole_0(A_155, B_156))), inference(resolution, [status(thm)], [c_98, c_4])).
% 12.38/4.55  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_1477, plain, (![B_158, B_156, A_157]: (~r2_hidden('#skF_2'(B_158, B_156, k3_xboole_0(A_157, B_158)), B_156) | r2_hidden('#skF_1'(B_158, B_156, k3_xboole_0(A_157, B_158)), B_156) | k3_xboole_0(B_158, B_156)=k3_xboole_0(A_157, B_158))), inference(resolution, [status(thm)], [c_1428, c_10])).
% 12.38/4.55  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_1484, plain, (![B_2, A_1, A_155, A_157, B_158]: (r2_hidden('#skF_1'(A_155, k3_xboole_0(A_1, B_2), k3_xboole_0(A_157, B_158)), A_1) | r2_hidden('#skF_2'(A_155, k3_xboole_0(A_1, B_2), k3_xboole_0(A_157, B_158)), B_158) | k3_xboole_0(A_157, B_158)=k3_xboole_0(A_155, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_1428, c_6])).
% 12.38/4.55  tff(c_225, plain, (![A_64, B_65, C_66]: (r2_hidden('#skF_1'(A_64, B_65, C_66), A_64) | r2_hidden('#skF_2'(A_64, B_65, C_66), C_66) | k3_xboole_0(A_64, B_65)=C_66)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_244, plain, (![A_64, B_65, A_1, B_2]: (r2_hidden('#skF_2'(A_64, B_65, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_64, B_65, k3_xboole_0(A_1, B_2)), A_64) | k3_xboole_0(A_64, B_65)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_225, c_4])).
% 12.38/4.55  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_1649, plain, (![A_172, B_173, A_174, B_175]: (r2_hidden('#skF_2'(A_172, B_173, k3_xboole_0(A_174, B_175)), k3_xboole_0(A_174, B_175)) | k3_xboole_0(A_174, B_175)=k3_xboole_0(A_172, B_173) | ~r2_hidden('#skF_1'(A_172, B_173, k3_xboole_0(A_174, B_175)), B_175) | ~r2_hidden('#skF_1'(A_172, B_173, k3_xboole_0(A_174, B_175)), A_174))), inference(resolution, [status(thm)], [c_2, c_246])).
% 12.38/4.55  tff(c_10080, plain, (![A_658, B_659, A_660, B_661]: (r2_hidden('#skF_2'(A_658, B_659, k3_xboole_0(A_660, B_661)), B_661) | k3_xboole_0(A_660, B_661)=k3_xboole_0(A_658, B_659) | ~r2_hidden('#skF_1'(A_658, B_659, k3_xboole_0(A_660, B_661)), B_661) | ~r2_hidden('#skF_1'(A_658, B_659, k3_xboole_0(A_660, B_661)), A_660))), inference(resolution, [status(thm)], [c_1649, c_4])).
% 12.38/4.55  tff(c_10685, plain, (![A_681, B_682, A_683]: (~r2_hidden('#skF_1'(A_681, B_682, k3_xboole_0(A_683, A_681)), A_683) | r2_hidden('#skF_2'(A_681, B_682, k3_xboole_0(A_683, A_681)), A_681) | k3_xboole_0(A_683, A_681)=k3_xboole_0(A_681, B_682))), inference(resolution, [status(thm)], [c_244, c_10080])).
% 12.38/4.55  tff(c_10799, plain, (![B_158, A_1, B_2]: (r2_hidden('#skF_2'(B_158, k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_158)), B_158) | k3_xboole_0(B_158, k3_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_158))), inference(resolution, [status(thm)], [c_1484, c_10685])).
% 12.38/4.55  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_342, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_1'(A_76, B_77, C_78), A_76) | ~r2_hidden('#skF_2'(A_76, B_77, C_78), B_77) | ~r2_hidden('#skF_2'(A_76, B_77, C_78), A_76) | k3_xboole_0(A_76, B_77)=C_78)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_357, plain, (![A_1, C_3]: (~r2_hidden('#skF_2'(A_1, C_3, C_3), A_1) | r2_hidden('#skF_1'(A_1, C_3, C_3), A_1) | k3_xboole_0(A_1, C_3)=C_3)), inference(resolution, [status(thm)], [c_18, c_342])).
% 12.38/4.55  tff(c_375, plain, (![A_81, B_82, C_83]: (~r2_hidden('#skF_1'(A_81, B_82, C_83), C_83) | ~r2_hidden('#skF_2'(A_81, B_82, C_83), B_82) | ~r2_hidden('#skF_2'(A_81, B_82, C_83), A_81) | k3_xboole_0(A_81, B_82)=C_83)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.38/4.55  tff(c_392, plain, (![A_84]: (~r2_hidden('#skF_2'(A_84, A_84, A_84), A_84) | k3_xboole_0(A_84, A_84)=A_84)), inference(resolution, [status(thm)], [c_357, c_375])).
% 12.38/4.55  tff(c_409, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_260, c_392])).
% 12.38/4.55  tff(c_261, plain, (![A_67, B_68, A_1, B_2]: (r2_hidden('#skF_2'(A_67, B_68, k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2)) | k3_xboole_0(A_67, B_68)=k3_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_67, B_68, k3_xboole_0(A_1, B_2)), B_2) | ~r2_hidden('#skF_1'(A_67, B_68, k3_xboole_0(A_1, B_2)), A_1))), inference(resolution, [status(thm)], [c_2, c_246])).
% 12.38/4.55  tff(c_2383, plain, (![A_229, B_230, A_231, B_232]: (~r2_hidden('#skF_2'(A_229, B_230, k3_xboole_0(A_231, B_232)), B_230) | ~r2_hidden('#skF_2'(A_229, B_230, k3_xboole_0(A_231, B_232)), A_229) | k3_xboole_0(A_231, B_232)=k3_xboole_0(A_229, B_230) | ~r2_hidden('#skF_1'(A_229, B_230, k3_xboole_0(A_231, B_232)), B_232) | ~r2_hidden('#skF_1'(A_229, B_230, k3_xboole_0(A_231, B_232)), A_231))), inference(resolution, [status(thm)], [c_2, c_375])).
% 12.38/4.55  tff(c_13075, plain, (![A_783, A_784, B_785]: (~r2_hidden('#skF_2'(A_783, k3_xboole_0(A_784, B_785), k3_xboole_0(A_784, B_785)), A_783) | k3_xboole_0(A_783, k3_xboole_0(A_784, B_785))=k3_xboole_0(A_784, B_785) | ~r2_hidden('#skF_1'(A_783, k3_xboole_0(A_784, B_785), k3_xboole_0(A_784, B_785)), B_785) | ~r2_hidden('#skF_1'(A_783, k3_xboole_0(A_784, B_785), k3_xboole_0(A_784, B_785)), A_784))), inference(resolution, [status(thm)], [c_261, c_2383])).
% 12.38/4.55  tff(c_13191, plain, (![A_783, B_2]: (~r2_hidden('#skF_2'(A_783, B_2, k3_xboole_0(B_2, B_2)), A_783) | k3_xboole_0(A_783, k3_xboole_0(B_2, B_2))=k3_xboole_0(B_2, B_2) | ~r2_hidden('#skF_1'(A_783, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2) | ~r2_hidden('#skF_1'(A_783, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2))), inference(superposition, [status(thm), theory('equality')], [c_409, c_13075])).
% 12.38/4.55  tff(c_13262, plain, (![A_786, B_787]: (~r2_hidden('#skF_2'(A_786, B_787, B_787), A_786) | k3_xboole_0(A_786, B_787)=B_787 | ~r2_hidden('#skF_1'(A_786, B_787, B_787), B_787) | ~r2_hidden('#skF_1'(A_786, B_787, B_787), B_787))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_409, c_409, c_409, c_409, c_409, c_409, c_13191])).
% 12.38/4.55  tff(c_13454, plain, (![B_788, A_789]: (~r2_hidden('#skF_1'(B_788, k3_xboole_0(A_789, B_788), k3_xboole_0(A_789, B_788)), k3_xboole_0(A_789, B_788)) | k3_xboole_0(B_788, k3_xboole_0(A_789, B_788))=k3_xboole_0(A_789, B_788))), inference(resolution, [status(thm)], [c_10799, c_13262])).
% 12.38/4.55  tff(c_13668, plain, (![B_796, A_797]: (~r2_hidden('#skF_2'(B_796, k3_xboole_0(A_797, B_796), k3_xboole_0(A_797, B_796)), k3_xboole_0(A_797, B_796)) | k3_xboole_0(B_796, k3_xboole_0(A_797, B_796))=k3_xboole_0(A_797, B_796))), inference(resolution, [status(thm)], [c_1477, c_13454])).
% 12.38/4.55  tff(c_13784, plain, (![A_798, A_799]: (k3_xboole_0(A_798, k3_xboole_0(A_799, A_798))=k3_xboole_0(A_799, A_798))), inference(resolution, [status(thm)], [c_260, c_13668])).
% 12.38/4.55  tff(c_40, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.38/4.55  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.38/4.55  tff(c_52, plain, (![A_34, B_35]: (r1_tarski(k3_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_40, c_22])).
% 12.38/4.55  tff(c_15228, plain, (![A_799, A_798]: (r1_tarski(k3_xboole_0(A_799, A_798), A_798))), inference(superposition, [status(thm), theory('equality')], [c_13784, c_52])).
% 12.38/4.55  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.38/4.55  tff(c_26, plain, (![A_14, B_15]: (v1_relat_1(k4_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.38/4.55  tff(c_49, plain, (![A_34, B_35]: (v1_relat_1(k3_xboole_0(A_34, B_35)) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_40, c_26])).
% 12.38/4.55  tff(c_32, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.38/4.55  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.38/4.55  tff(c_208, plain, (![C_61, A_62, B_63]: (r1_tarski(k5_relat_1(C_61, A_62), k5_relat_1(C_61, B_63)) | ~r1_tarski(A_62, B_63) | ~v1_relat_1(C_61) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.38/4.55  tff(c_192, plain, (![C_58, A_59, B_60]: (r1_tarski(k5_relat_1(C_58, A_59), k5_relat_1(C_58, B_60)) | ~r1_tarski(A_59, B_60) | ~v1_relat_1(C_58) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.38/4.55  tff(c_84, plain, (![A_45, B_46, C_47]: (r1_tarski(A_45, k3_xboole_0(B_46, C_47)) | ~r1_tarski(A_45, C_47) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.38/4.55  tff(c_30, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.38/4.55  tff(c_88, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_30])).
% 12.38/4.55  tff(c_191, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_88])).
% 12.38/4.55  tff(c_195, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_192, c_191])).
% 12.38/4.55  tff(c_198, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_52, c_195])).
% 12.38/4.55  tff(c_201, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_49, c_198])).
% 12.38/4.55  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_201])).
% 12.38/4.55  tff(c_206, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_88])).
% 12.38/4.55  tff(c_211, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_208, c_206])).
% 12.38/4.55  tff(c_214, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_211])).
% 12.38/4.55  tff(c_215, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_214])).
% 12.38/4.55  tff(c_218, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_49, c_215])).
% 12.38/4.55  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_218])).
% 12.38/4.55  tff(c_223, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_214])).
% 12.38/4.55  tff(c_15697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15228, c_223])).
% 12.38/4.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.38/4.55  
% 12.38/4.55  Inference rules
% 12.38/4.55  ----------------------
% 12.38/4.55  #Ref     : 0
% 12.38/4.55  #Sup     : 3358
% 12.38/4.55  #Fact    : 0
% 12.38/4.55  #Define  : 0
% 12.38/4.55  #Split   : 2
% 12.38/4.55  #Chain   : 0
% 12.38/4.55  #Close   : 0
% 12.38/4.55  
% 12.38/4.55  Ordering : KBO
% 12.38/4.55  
% 12.38/4.55  Simplification rules
% 12.38/4.55  ----------------------
% 12.38/4.55  #Subsume      : 1516
% 12.38/4.55  #Demod        : 3942
% 12.38/4.55  #Tautology    : 374
% 12.38/4.55  #SimpNegUnit  : 0
% 12.38/4.55  #BackRed      : 3
% 12.38/4.55  
% 12.38/4.55  #Partial instantiations: 0
% 12.38/4.55  #Strategies tried      : 1
% 12.38/4.55  
% 12.38/4.55  Timing (in seconds)
% 12.38/4.55  ----------------------
% 12.38/4.55  Preprocessing        : 0.28
% 12.38/4.55  Parsing              : 0.15
% 12.38/4.55  CNF conversion       : 0.02
% 12.38/4.55  Main loop            : 3.50
% 12.38/4.55  Inferencing          : 1.08
% 12.38/4.55  Reduction            : 0.92
% 12.38/4.55  Demodulation         : 0.70
% 12.38/4.55  BG Simplification    : 0.10
% 12.38/4.55  Subsumption          : 1.22
% 12.38/4.55  Abstraction          : 0.23
% 12.38/4.55  MUC search           : 0.00
% 12.38/4.55  Cooper               : 0.00
% 12.38/4.55  Total                : 3.81
% 12.38/4.55  Index Insertion      : 0.00
% 12.38/4.56  Index Deletion       : 0.00
% 12.38/4.56  Index Matching       : 0.00
% 12.38/4.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
