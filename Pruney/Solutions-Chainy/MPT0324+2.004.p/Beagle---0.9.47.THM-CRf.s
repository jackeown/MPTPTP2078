%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:20 EST 2020

% Result     : Theorem 27.73s
% Output     : CNFRefutation 28.64s
% Verified   : 
% Statistics : Number of formulae       :  932 (48065 expanded)
%              Number of leaves         :   20 (15616 expanded)
%              Depth                    :   22
%              Number of atoms          : 1294 (117947 expanded)
%              Number of equality atoms :    3 (12492 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( r2_hidden(A,k2_zfmisc_1(B,C))
          & r2_hidden(A,k2_zfmisc_1(D,E)) )
       => r2_hidden(A,k2_zfmisc_1(k3_xboole_0(B,D),k3_xboole_0(C,E))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_7','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_55,plain,(
    ! [A_37,B_38,C_39] :
      ( k4_tarski('#skF_3'(A_37,B_38,C_39),'#skF_4'(A_37,B_38,C_39)) = A_37
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_12,C_14,B_13,D_15] :
      ( r2_hidden(A_12,C_14)
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,D_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_219,plain,(
    ! [D_70,C_72,B_69,C_71,A_68] :
      ( r2_hidden('#skF_3'(A_68,B_69,C_71),C_72)
      | ~ r2_hidden(A_68,k2_zfmisc_1(C_72,D_70))
      | ~ r2_hidden(A_68,k2_zfmisc_1(B_69,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_26])).

tff(c_252,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_3'('#skF_5',B_69,C_71),'#skF_6')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_30,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_251,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_3'('#skF_5',B_69,C_71),'#skF_8')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_30,c_219])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [B_13,D_15,A_12,C_14] :
      ( r2_hidden(B_13,D_15)
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,D_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_166,plain,(
    ! [A_56,B_57,C_60,C_59,D_58] :
      ( r2_hidden('#skF_4'(A_56,B_57,C_59),D_58)
      | ~ r2_hidden(A_56,k2_zfmisc_1(C_60,D_58))
      | ~ r2_hidden(A_56,k2_zfmisc_1(B_57,C_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_24])).

tff(c_199,plain,(
    ! [B_57,C_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_57,C_59),'#skF_7')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_32,c_166])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,D_15))
      | ~ r2_hidden(B_13,D_15)
      | ~ r2_hidden(A_12,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1321,plain,(
    ! [C_162,D_161,C_163,A_159,B_160] :
      ( r2_hidden(A_159,k2_zfmisc_1(C_163,D_161))
      | ~ r2_hidden('#skF_4'(A_159,B_160,C_162),D_161)
      | ~ r2_hidden('#skF_3'(A_159,B_160,C_162),C_163)
      | ~ r2_hidden(A_159,k2_zfmisc_1(B_160,C_162)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_22])).

tff(c_1338,plain,(
    ! [C_164,B_165,C_166] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_164,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_165,C_166),C_164)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_165,C_166)) ) ),
    inference(resolution,[status(thm)],[c_199,c_1321])).

tff(c_3221,plain,(
    ! [A_268,B_269,B_270,C_271] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_268,B_269),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_270,C_271))
      | ~ r2_hidden('#skF_3'('#skF_5',B_270,C_271),B_269)
      | ~ r2_hidden('#skF_3'('#skF_5',B_270,C_271),A_268) ) ),
    inference(resolution,[status(thm)],[c_2,c_1338])).

tff(c_3657,plain,(
    ! [A_290,B_291,C_292] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_290,'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_291,C_292),A_290)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_291,C_292)) ) ),
    inference(resolution,[status(thm)],[c_251,c_3221])).

tff(c_3671,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_252,c_3657])).

tff(c_3687,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_3671])).

tff(c_3232,plain,(
    ! [A_272,B_273,C_274] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_272,'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_273,C_274),A_272)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_273,C_274)) ) ),
    inference(resolution,[status(thm)],[c_252,c_3221])).

tff(c_3242,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_251,c_3232])).

tff(c_3244,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_3242])).

tff(c_198,plain,(
    ! [B_57,C_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_57,C_59),'#skF_9')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_1526,plain,(
    ! [C_174,B_175,C_176] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_174,'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_175,C_176),C_174)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_175,C_176)) ) ),
    inference(resolution,[status(thm)],[c_198,c_1321])).

tff(c_1537,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6','#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_252,c_1526])).

tff(c_1541,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_1537])).

tff(c_1351,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_251,c_1338])).

tff(c_1353,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_1351])).

tff(c_1357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1353,c_30])).

tff(c_1358,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1351])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1541,c_1358])).

tff(c_1548,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1537])).

tff(c_3253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3244,c_1548])).

tff(c_3254,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3242])).

tff(c_67,plain,(
    ! [C_39,B_38,D_15,A_37,C_14] :
      ( r2_hidden('#skF_3'(A_37,B_38,C_39),C_14)
      | ~ r2_hidden(A_37,k2_zfmisc_1(C_14,D_15))
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_26])).

tff(c_3267,plain,(
    ! [B_275,C_276] :
      ( r2_hidden('#skF_3'('#skF_5',B_275,C_276),k3_xboole_0('#skF_8','#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_275,C_276)) ) ),
    inference(resolution,[status(thm)],[c_3254,c_67])).

tff(c_3229,plain,(
    ! [A_268,B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_268,'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_69,C_71),A_268)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_252,c_3221])).

tff(c_3296,plain,(
    ! [B_275,C_276] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_275,C_276)) ) ),
    inference(resolution,[status(thm)],[c_3267,c_3229])).

tff(c_3433,plain,(
    ! [B_275,C_276] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_275,C_276)) ),
    inference(splitLeft,[status(thm)],[c_3296])).

tff(c_1336,plain,(
    ! [C_163,B_57,C_59] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_163,'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_57,C_59),C_163)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_198,c_1321])).

tff(c_3298,plain,(
    ! [B_275,C_276] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_275,C_276)) ) ),
    inference(resolution,[status(thm)],[c_3267,c_1336])).

tff(c_3309,plain,(
    ! [B_275,C_276] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_275,C_276)) ),
    inference(splitLeft,[status(thm)],[c_3298])).

tff(c_3419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3309,c_3254])).

tff(c_3420,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3298])).

tff(c_3460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3433,c_3420])).

tff(c_3461,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3296])).

tff(c_3474,plain,(
    ! [B_284,C_285] :
      ( r2_hidden('#skF_3'('#skF_5',B_284,C_285),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_284,C_285)) ) ),
    inference(resolution,[status(thm)],[c_3461,c_67])).

tff(c_3503,plain,(
    ! [B_284,C_285] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_284,C_285)) ) ),
    inference(resolution,[status(thm)],[c_3474,c_3229])).

tff(c_3642,plain,(
    ! [B_284,C_285] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_284,C_285)) ),
    inference(splitLeft,[status(thm)],[c_3503])).

tff(c_3505,plain,(
    ! [B_284,C_285] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_284,C_285)) ) ),
    inference(resolution,[status(thm)],[c_3474,c_1336])).

tff(c_3516,plain,(
    ! [B_284,C_285] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_284,C_285)) ),
    inference(splitLeft,[status(thm)],[c_3505])).

tff(c_3528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3516,c_3461])).

tff(c_3529,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3505])).

tff(c_3655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3642,c_3529])).

tff(c_3656,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3503])).

tff(c_3702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3687,c_3656])).

tff(c_3703,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3671])).

tff(c_3714,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0('#skF_6','#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3703,c_67])).

tff(c_48272,plain,(
    ! [A_951,C_946,B_950,A_949,C_947,B_948] :
      ( r2_hidden(A_949,k2_zfmisc_1(C_947,k3_xboole_0(A_951,B_950)))
      | ~ r2_hidden('#skF_3'(A_949,B_948,C_946),C_947)
      | ~ r2_hidden(A_949,k2_zfmisc_1(B_948,C_946))
      | ~ r2_hidden('#skF_4'(A_949,B_948,C_946),B_950)
      | ~ r2_hidden('#skF_4'(A_949,B_948,C_946),A_951) ) ),
    inference(resolution,[status(thm)],[c_2,c_1321])).

tff(c_55636,plain,(
    ! [A_1066,B_1067,B_1068,C_1069] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1066,B_1067)))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1068,C_1069),B_1067)
      | ~ r2_hidden('#skF_4'('#skF_5',B_1068,C_1069),A_1066)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1068,C_1069)) ) ),
    inference(resolution,[status(thm)],[c_251,c_48272])).

tff(c_56413,plain,(
    ! [A_1081,B_1082,C_1083] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1081,'#skF_9')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1082,C_1083),A_1081)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1082,C_1083)) ) ),
    inference(resolution,[status(thm)],[c_198,c_55636])).

tff(c_56424,plain,(
    ! [B_57,C_59] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_199,c_56413])).

tff(c_56428,plain,(
    ! [B_57,C_59] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ),
    inference(splitLeft,[status(thm)],[c_56424])).

tff(c_55647,plain,(
    ! [A_1070,B_1071,C_1072] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1070,'#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1071,C_1072),A_1070)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1071,C_1072)) ) ),
    inference(resolution,[status(thm)],[c_199,c_55636])).

tff(c_55657,plain,(
    ! [B_57,C_59] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_9','#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_198,c_55647])).

tff(c_55659,plain,(
    ! [B_57,C_59] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ),
    inference(splitLeft,[status(thm)],[c_55657])).

tff(c_1352,plain,(
    ! [A_1,B_2,B_165,C_166] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_1,B_2),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_165,C_166))
      | ~ r2_hidden('#skF_3'('#skF_5',B_165,C_166),B_2)
      | ~ r2_hidden('#skF_3'('#skF_5',B_165,C_166),A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_1338])).

tff(c_31034,plain,(
    ! [A_791,B_792,C_793] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_791,k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_792,C_793),A_791)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_792,C_793)) ) ),
    inference(resolution,[status(thm)],[c_3267,c_1352])).

tff(c_31198,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3714,c_31034])).

tff(c_34201,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_31198])).

tff(c_31203,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_251,c_31034])).

tff(c_31622,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_31203])).

tff(c_31202,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_252,c_31034])).

tff(c_31205,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_31202])).

tff(c_3716,plain,(
    ! [B_293,C_294] :
      ( r2_hidden('#skF_3'('#skF_5',B_293,C_294),k3_xboole_0('#skF_6','#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ) ),
    inference(resolution,[status(thm)],[c_3703,c_67])).

tff(c_13496,plain,(
    ! [A_551,B_552,C_553] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_551,k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_552,C_553),A_551)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_552,C_553)) ) ),
    inference(resolution,[status(thm)],[c_3716,c_1352])).

tff(c_13596,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_251,c_13496])).

tff(c_13699,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_13596])).

tff(c_13595,plain,(
    ! [B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_252,c_13496])).

tff(c_13605,plain,(
    ! [B_69,C_71] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ),
    inference(splitLeft,[status(thm)],[c_13595])).

tff(c_3265,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0('#skF_8','#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3254,c_67])).

tff(c_3670,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3265,c_3657])).

tff(c_3950,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_3670])).

tff(c_3748,plain,(
    ! [B_293,C_294] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ) ),
    inference(resolution,[status(thm)],[c_3716,c_3229])).

tff(c_3919,plain,(
    ! [B_293,C_294] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ),
    inference(splitLeft,[status(thm)],[c_3748])).

tff(c_3750,plain,(
    ! [B_293,C_294] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ) ),
    inference(resolution,[status(thm)],[c_3716,c_1336])).

tff(c_3845,plain,(
    ! [B_293,C_294] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ),
    inference(splitLeft,[status(thm)],[c_3750])).

tff(c_3861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3845,c_3703])).

tff(c_3862,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3750])).

tff(c_3936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3919,c_3862])).

tff(c_3937,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3748])).

tff(c_3968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3950,c_3937])).

tff(c_3969,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3670])).

tff(c_4201,plain,(
    ! [B_316,C_317] :
      ( r2_hidden('#skF_3'('#skF_5',B_316,C_317),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_316,C_317)) ) ),
    inference(resolution,[status(thm)],[c_3969,c_67])).

tff(c_4233,plain,(
    ! [B_316,C_317] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_316,C_317)) ) ),
    inference(resolution,[status(thm)],[c_4201,c_3229])).

tff(c_5071,plain,(
    ! [B_316,C_317] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_316,C_317)) ),
    inference(splitLeft,[status(thm)],[c_4233])).

tff(c_4407,plain,(
    ! [B_323,C_324] :
      ( r2_hidden('#skF_3'('#skF_5',B_323,C_324),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_323,C_324)) ) ),
    inference(resolution,[status(thm)],[c_3937,c_67])).

tff(c_4439,plain,(
    ! [B_323,C_324] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_323,C_324)) ) ),
    inference(resolution,[status(thm)],[c_4407,c_3229])).

tff(c_5031,plain,(
    ! [B_323,C_324] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_323,C_324)) ),
    inference(splitLeft,[status(thm)],[c_4439])).

tff(c_3230,plain,(
    ! [A_268,B_69,C_71] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_268,'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_69,C_71),A_268)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_69,C_71)) ) ),
    inference(resolution,[status(thm)],[c_251,c_3221])).

tff(c_3747,plain,(
    ! [B_293,C_294] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ) ),
    inference(resolution,[status(thm)],[c_3716,c_3230])).

tff(c_4119,plain,(
    ! [B_293,C_294] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ),
    inference(splitLeft,[status(thm)],[c_3747])).

tff(c_4138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4119,c_3969])).

tff(c_4139,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3747])).

tff(c_4487,plain,(
    ! [B_325,C_326] :
      ( r2_hidden('#skF_3'('#skF_5',B_325,C_326),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_325,C_326)) ) ),
    inference(resolution,[status(thm)],[c_4139,c_67])).

tff(c_4518,plain,(
    ! [B_325,C_326] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_325,C_326)) ) ),
    inference(resolution,[status(thm)],[c_4487,c_3230])).

tff(c_4840,plain,(
    ! [B_325,C_326] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_325,C_326)) ),
    inference(splitLeft,[status(thm)],[c_4518])).

tff(c_4519,plain,(
    ! [B_325,C_326] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_325,C_326)) ) ),
    inference(resolution,[status(thm)],[c_4487,c_3229])).

tff(c_4802,plain,(
    ! [B_325,C_326] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_325,C_326)) ),
    inference(splitLeft,[status(thm)],[c_4519])).

tff(c_4232,plain,(
    ! [B_316,C_317] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_316,C_317)) ) ),
    inference(resolution,[status(thm)],[c_4201,c_3230])).

tff(c_4720,plain,(
    ! [B_316,C_317] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_316,C_317)) ),
    inference(splitLeft,[status(thm)],[c_4232])).

tff(c_4521,plain,(
    ! [B_325,C_326] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_325,C_326)) ) ),
    inference(resolution,[status(thm)],[c_4487,c_1336])).

tff(c_4532,plain,(
    ! [B_325,C_326] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_325,C_326)) ),
    inference(splitLeft,[status(thm)],[c_4521])).

tff(c_4441,plain,(
    ! [B_323,C_324] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_323,C_324)) ) ),
    inference(resolution,[status(thm)],[c_4407,c_1336])).

tff(c_4452,plain,(
    ! [B_323,C_324] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_323,C_324)) ),
    inference(splitLeft,[status(thm)],[c_4441])).

tff(c_4235,plain,(
    ! [B_316,C_317] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_316,C_317)) ) ),
    inference(resolution,[status(thm)],[c_4201,c_1336])).

tff(c_4246,plain,(
    ! [B_316,C_317] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_316,C_317)) ),
    inference(splitLeft,[status(thm)],[c_4235])).

tff(c_4266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4246,c_4139])).

tff(c_4267,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_4235])).

tff(c_4473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4452,c_4267])).

tff(c_4474,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_4441])).

tff(c_4554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4532,c_4474])).

tff(c_4555,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_4521])).

tff(c_4743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4720,c_4555])).

tff(c_4744,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4232])).

tff(c_4826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4802,c_4744])).

tff(c_4827,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4519])).

tff(c_4865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4840,c_4827])).

tff(c_4866,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4518])).

tff(c_5057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5031,c_4866])).

tff(c_5058,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4439])).

tff(c_5098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5071,c_5058])).

tff(c_5099,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4233])).

tff(c_6069,plain,(
    ! [B_368,C_369] :
      ( r2_hidden('#skF_3'('#skF_5',B_368,C_369),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_368,C_369)) ) ),
    inference(resolution,[status(thm)],[c_5099,c_67])).

tff(c_6100,plain,(
    ! [B_368,C_369] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_368,C_369)) ) ),
    inference(resolution,[status(thm)],[c_6069,c_3230])).

tff(c_8892,plain,(
    ! [B_368,C_369] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_368,C_369)) ),
    inference(splitLeft,[status(thm)],[c_6100])).

tff(c_6163,plain,(
    ! [B_370,C_371] :
      ( r2_hidden('#skF_3'('#skF_5',B_370,C_371),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_370,C_371)) ) ),
    inference(resolution,[status(thm)],[c_4744,c_67])).

tff(c_6194,plain,(
    ! [B_370,C_371] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_370,C_371)) ) ),
    inference(resolution,[status(thm)],[c_6163,c_3230])).

tff(c_8816,plain,(
    ! [B_370,C_371] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_370,C_371)) ),
    inference(splitLeft,[status(thm)],[c_6194])).

tff(c_3472,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3461,c_67])).

tff(c_3669,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3472,c_3657])).

tff(c_5112,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_3669])).

tff(c_5280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5112,c_5099])).

tff(c_5281,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3669])).

tff(c_5839,plain,(
    ! [B_361,C_362] :
      ( r2_hidden('#skF_3'('#skF_5',B_361,C_362),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_361,C_362)) ) ),
    inference(resolution,[status(thm)],[c_5281,c_67])).

tff(c_5871,plain,(
    ! [B_361,C_362] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_361,C_362)) ) ),
    inference(resolution,[status(thm)],[c_5839,c_3229])).

tff(c_8600,plain,(
    ! [B_361,C_362] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_361,C_362)) ),
    inference(splitLeft,[status(thm)],[c_5871])).

tff(c_5870,plain,(
    ! [B_361,C_362] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_361,C_362)) ) ),
    inference(resolution,[status(thm)],[c_5839,c_3230])).

tff(c_8536,plain,(
    ! [B_361,C_362] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_361,C_362)) ),
    inference(splitLeft,[status(thm)],[c_5870])).

tff(c_5337,plain,(
    ! [B_348,C_349] :
      ( r2_hidden('#skF_3'('#skF_5',B_348,C_349),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_348,C_349)) ) ),
    inference(resolution,[status(thm)],[c_4866,c_67])).

tff(c_5369,plain,(
    ! [B_348,C_349] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_348,C_349)) ) ),
    inference(resolution,[status(thm)],[c_5337,c_3229])).

tff(c_8065,plain,(
    ! [B_348,C_349] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_348,C_349)) ),
    inference(splitLeft,[status(thm)],[c_5369])).

tff(c_4438,plain,(
    ! [B_323,C_324] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_323,C_324)) ) ),
    inference(resolution,[status(thm)],[c_4407,c_3230])).

tff(c_5294,plain,(
    ! [B_323,C_324] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_323,C_324)) ),
    inference(splitLeft,[status(thm)],[c_4438])).

tff(c_5323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5294,c_5281])).

tff(c_5324,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4438])).

tff(c_5747,plain,(
    ! [B_359,C_360] :
      ( r2_hidden('#skF_3'('#skF_5',B_359,C_360),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_359,C_360)) ) ),
    inference(resolution,[status(thm)],[c_5324,c_67])).

tff(c_5778,plain,(
    ! [B_359,C_360] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_359,C_360)) ) ),
    inference(resolution,[status(thm)],[c_5747,c_3230])).

tff(c_7876,plain,(
    ! [B_359,C_360] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_359,C_360)) ),
    inference(splitLeft,[status(thm)],[c_5778])).

tff(c_6385,plain,(
    ! [B_377,C_378] :
      ( r2_hidden('#skF_3'('#skF_5',B_377,C_378),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_377,C_378)) ) ),
    inference(resolution,[status(thm)],[c_5058,c_67])).

tff(c_6416,plain,(
    ! [B_377,C_378] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_377,C_378)) ) ),
    inference(resolution,[status(thm)],[c_6385,c_3230])).

tff(c_7424,plain,(
    ! [B_377,C_378] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_377,C_378)) ),
    inference(splitLeft,[status(thm)],[c_6416])).

tff(c_5566,plain,(
    ! [B_355,C_356] :
      ( r2_hidden('#skF_3'('#skF_5',B_355,C_356),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_355,C_356)) ) ),
    inference(resolution,[status(thm)],[c_3656,c_67])).

tff(c_5598,plain,(
    ! [B_355,C_356] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_355,C_356)) ) ),
    inference(resolution,[status(thm)],[c_5566,c_3229])).

tff(c_7237,plain,(
    ! [B_355,C_356] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_355,C_356)) ),
    inference(splitLeft,[status(thm)],[c_5598])).

tff(c_5779,plain,(
    ! [B_359,C_360] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_359,C_360)) ) ),
    inference(resolution,[status(thm)],[c_5747,c_3229])).

tff(c_7181,plain,(
    ! [B_359,C_360] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_359,C_360)) ),
    inference(splitLeft,[status(thm)],[c_5779])).

tff(c_5368,plain,(
    ! [B_348,C_349] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_348,C_349)) ) ),
    inference(resolution,[status(thm)],[c_5337,c_3230])).

tff(c_7126,plain,(
    ! [B_348,C_349] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_348,C_349)) ),
    inference(splitLeft,[status(thm)],[c_5368])).

tff(c_5597,plain,(
    ! [B_355,C_356] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_355,C_356)) ) ),
    inference(resolution,[status(thm)],[c_5566,c_3230])).

tff(c_6858,plain,(
    ! [B_355,C_356] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_355,C_356)) ),
    inference(splitLeft,[status(thm)],[c_5597])).

tff(c_5656,plain,(
    ! [B_357,C_358] :
      ( r2_hidden('#skF_3'('#skF_5',B_357,C_358),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_357,C_358)) ) ),
    inference(resolution,[status(thm)],[c_4827,c_67])).

tff(c_5688,plain,(
    ! [B_357,C_358] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_357,C_358)) ) ),
    inference(resolution,[status(thm)],[c_5656,c_3229])).

tff(c_6805,plain,(
    ! [B_357,C_358] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_357,C_358)) ),
    inference(splitLeft,[status(thm)],[c_5688])).

tff(c_6195,plain,(
    ! [B_370,C_371] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_370,C_371)) ) ),
    inference(resolution,[status(thm)],[c_6163,c_3229])).

tff(c_6601,plain,(
    ! [B_370,C_371] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_370,C_371)) ),
    inference(splitLeft,[status(thm)],[c_6195])).

tff(c_6419,plain,(
    ! [B_377,C_378] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_377,C_378)) ) ),
    inference(resolution,[status(thm)],[c_6385,c_1336])).

tff(c_6430,plain,(
    ! [B_377,C_378] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_377,C_378)) ),
    inference(splitLeft,[status(thm)],[c_6419])).

tff(c_6197,plain,(
    ! [B_370,C_371] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_370,C_371)) ) ),
    inference(resolution,[status(thm)],[c_6163,c_1336])).

tff(c_6208,plain,(
    ! [B_370,C_371] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_370,C_371)) ),
    inference(splitLeft,[status(thm)],[c_6197])).

tff(c_6103,plain,(
    ! [B_368,C_369] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_368,C_369)) ) ),
    inference(resolution,[status(thm)],[c_6069,c_1336])).

tff(c_6114,plain,(
    ! [B_368,C_369] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_368,C_369)) ),
    inference(splitLeft,[status(thm)],[c_6103])).

tff(c_5873,plain,(
    ! [B_361,C_362] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_361,C_362)) ) ),
    inference(resolution,[status(thm)],[c_5839,c_1336])).

tff(c_5884,plain,(
    ! [B_361,C_362] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_361,C_362)) ),
    inference(splitLeft,[status(thm)],[c_5873])).

tff(c_5781,plain,(
    ! [B_359,C_360] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_359,C_360)) ) ),
    inference(resolution,[status(thm)],[c_5747,c_1336])).

tff(c_5792,plain,(
    ! [B_359,C_360] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_359,C_360)) ),
    inference(splitLeft,[status(thm)],[c_5781])).

tff(c_5690,plain,(
    ! [B_357,C_358] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_357,C_358)) ) ),
    inference(resolution,[status(thm)],[c_5656,c_1336])).

tff(c_5701,plain,(
    ! [B_357,C_358] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_357,C_358)) ),
    inference(splitLeft,[status(thm)],[c_5690])).

tff(c_5600,plain,(
    ! [B_355,C_356] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_355,C_356)) ) ),
    inference(resolution,[status(thm)],[c_5566,c_1336])).

tff(c_5611,plain,(
    ! [B_355,C_356] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_355,C_356)) ),
    inference(splitLeft,[status(thm)],[c_5600])).

tff(c_5371,plain,(
    ! [B_348,C_349] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_348,C_349)) ) ),
    inference(resolution,[status(thm)],[c_5337,c_1336])).

tff(c_5382,plain,(
    ! [B_348,C_349] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_348,C_349)) ),
    inference(splitLeft,[status(thm)],[c_5371])).

tff(c_5412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5382,c_5324])).

tff(c_5413,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5371])).

tff(c_5642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5611,c_5413])).

tff(c_5643,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5600])).

tff(c_5733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5701,c_5643])).

tff(c_5734,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5690])).

tff(c_5825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5792,c_5734])).

tff(c_5826,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5781])).

tff(c_5918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5884,c_5826])).

tff(c_5919,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5873])).

tff(c_6149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6114,c_5919])).

tff(c_6150,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6103])).

tff(c_6244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6208,c_6150])).

tff(c_6245,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6197])).

tff(c_6467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6430,c_6245])).

tff(c_6468,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6419])).

tff(c_6791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6601,c_6468])).

tff(c_6792,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6195])).

tff(c_6844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6805,c_6792])).

tff(c_6845,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5688])).

tff(c_6898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6858,c_6845])).

tff(c_6899,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5597])).

tff(c_7167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7126,c_6899])).

tff(c_7168,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5368])).

tff(c_7223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7181,c_7168])).

tff(c_7224,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5779])).

tff(c_7410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7237,c_7224])).

tff(c_7411,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5598])).

tff(c_7862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7424,c_7411])).

tff(c_7863,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6416])).

tff(c_7921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7876,c_7863])).

tff(c_7922,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5778])).

tff(c_8111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8065,c_7922])).

tff(c_8112,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5369])).

tff(c_8583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8536,c_8112])).

tff(c_8584,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5870])).

tff(c_8648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8600,c_8584])).

tff(c_8649,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5871])).

tff(c_8865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8816,c_8649])).

tff(c_8866,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6194])).

tff(c_8942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8892,c_8866])).

tff(c_8943,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6100])).

tff(c_13183,plain,(
    ! [B_544,C_545] :
      ( r2_hidden('#skF_3'('#skF_5',B_544,C_545),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_544,C_545)) ) ),
    inference(resolution,[status(thm)],[c_8943,c_67])).

tff(c_13217,plain,(
    ! [B_544,C_545] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_544,C_545)) ) ),
    inference(resolution,[status(thm)],[c_13183,c_1336])).

tff(c_13228,plain,(
    ! [B_544,C_545] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_544,C_545)) ),
    inference(splitLeft,[status(thm)],[c_13217])).

tff(c_5687,plain,(
    ! [B_357,C_358] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_357,C_358)) ) ),
    inference(resolution,[status(thm)],[c_5656,c_3230])).

tff(c_9027,plain,(
    ! [B_357,C_358] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_357,C_358)) ),
    inference(splitLeft,[status(thm)],[c_5687])).

tff(c_6101,plain,(
    ! [B_368,C_369] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_368,C_369)) ) ),
    inference(resolution,[status(thm)],[c_6069,c_3229])).

tff(c_8959,plain,(
    ! [B_368,C_369] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_368,C_369)) ),
    inference(splitLeft,[status(thm)],[c_6101])).

tff(c_9010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8959,c_8943])).

tff(c_9011,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6101])).

tff(c_9089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9027,c_9011])).

tff(c_9090,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5687])).

tff(c_13040,plain,(
    ! [B_538,C_539] :
      ( r2_hidden('#skF_3'('#skF_5',B_538,C_539),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_538,C_539)) ) ),
    inference(resolution,[status(thm)],[c_9090,c_67])).

tff(c_13074,plain,(
    ! [B_538,C_539] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_538,C_539)) ) ),
    inference(resolution,[status(thm)],[c_13040,c_1336])).

tff(c_13092,plain,(
    ! [B_538,C_539] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_538,C_539)) ),
    inference(splitLeft,[status(thm)],[c_13074])).

tff(c_12754,plain,(
    ! [B_531,C_532] :
      ( r2_hidden('#skF_3'('#skF_5',B_531,C_532),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_531,C_532)) ) ),
    inference(resolution,[status(thm)],[c_8866,c_67])).

tff(c_12788,plain,(
    ! [B_531,C_532] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_531,C_532)) ) ),
    inference(resolution,[status(thm)],[c_12754,c_1336])).

tff(c_12799,plain,(
    ! [B_531,C_532] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_531,C_532)) ),
    inference(splitLeft,[status(thm)],[c_12788])).

tff(c_12112,plain,(
    ! [B_522,C_523] :
      ( r2_hidden('#skF_3'('#skF_5',B_522,C_523),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_522,C_523)) ) ),
    inference(resolution,[status(thm)],[c_7922,c_67])).

tff(c_12146,plain,(
    ! [B_522,C_523] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_522,C_523)) ) ),
    inference(resolution,[status(thm)],[c_12112,c_1336])).

tff(c_12665,plain,(
    ! [B_522,C_523] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_522,C_523)) ),
    inference(splitLeft,[status(thm)],[c_12146])).

tff(c_11814,plain,(
    ! [B_515,C_516] :
      ( r2_hidden('#skF_3'('#skF_5',B_515,C_516),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_515,C_516)) ) ),
    inference(resolution,[status(thm)],[c_6845,c_67])).

tff(c_11848,plain,(
    ! [B_515,C_516] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_515,C_516)) ) ),
    inference(resolution,[status(thm)],[c_11814,c_1336])).

tff(c_11859,plain,(
    ! [B_515,C_516] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_515,C_516)) ),
    inference(splitLeft,[status(thm)],[c_11848])).

tff(c_6417,plain,(
    ! [B_377,C_378] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_377,C_378)) ) ),
    inference(resolution,[status(thm)],[c_6385,c_3229])).

tff(c_9106,plain,(
    ! [B_377,C_378] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_377,C_378)) ),
    inference(splitLeft,[status(thm)],[c_6417])).

tff(c_9159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9106,c_9090])).

tff(c_9160,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6417])).

tff(c_11675,plain,(
    ! [B_509,C_510] :
      ( r2_hidden('#skF_3'('#skF_5',B_509,C_510),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_509,C_510)) ) ),
    inference(resolution,[status(thm)],[c_9160,c_67])).

tff(c_11709,plain,(
    ! [B_509,C_510] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_509,C_510)) ) ),
    inference(resolution,[status(thm)],[c_11675,c_1336])).

tff(c_11730,plain,(
    ! [B_509,C_510] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_509,C_510)) ),
    inference(splitLeft,[status(thm)],[c_11709])).

tff(c_11385,plain,(
    ! [B_502,C_503] :
      ( r2_hidden('#skF_3'('#skF_5',B_502,C_503),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_502,C_503)) ) ),
    inference(resolution,[status(thm)],[c_7168,c_67])).

tff(c_11419,plain,(
    ! [B_502,C_503] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_502,C_503)) ) ),
    inference(resolution,[status(thm)],[c_11385,c_1336])).

tff(c_11430,plain,(
    ! [B_502,C_503] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_502,C_503)) ),
    inference(splitLeft,[status(thm)],[c_11419])).

tff(c_11248,plain,(
    ! [B_496,C_497] :
      ( r2_hidden('#skF_3'('#skF_5',B_496,C_497),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_496,C_497)) ) ),
    inference(resolution,[status(thm)],[c_8584,c_67])).

tff(c_11282,plain,(
    ! [B_496,C_497] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_496,C_497)) ) ),
    inference(resolution,[status(thm)],[c_11248,c_1336])).

tff(c_11303,plain,(
    ! [B_496,C_497] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_496,C_497)) ),
    inference(splitLeft,[status(thm)],[c_11282])).

tff(c_10880,plain,(
    ! [B_485,C_486] :
      ( r2_hidden('#skF_3'('#skF_5',B_485,C_486),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_485,C_486)) ) ),
    inference(resolution,[status(thm)],[c_7411,c_67])).

tff(c_10914,plain,(
    ! [B_485,C_486] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_485,C_486)) ) ),
    inference(resolution,[status(thm)],[c_10880,c_1336])).

tff(c_10925,plain,(
    ! [B_485,C_486] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_485,C_486)) ),
    inference(splitLeft,[status(thm)],[c_10914])).

tff(c_10745,plain,(
    ! [B_479,C_480] :
      ( r2_hidden('#skF_3'('#skF_5',B_479,C_480),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_479,C_480)) ) ),
    inference(resolution,[status(thm)],[c_6792,c_67])).

tff(c_10779,plain,(
    ! [B_479,C_480] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_479,C_480)) ) ),
    inference(resolution,[status(thm)],[c_10745,c_1336])).

tff(c_10790,plain,(
    ! [B_479,C_480] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_479,C_480)) ),
    inference(splitLeft,[status(thm)],[c_10779])).

tff(c_10475,plain,(
    ! [B_472,C_473] :
      ( r2_hidden('#skF_3'('#skF_5',B_472,C_473),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_472,C_473)) ) ),
    inference(resolution,[status(thm)],[c_6899,c_67])).

tff(c_10509,plain,(
    ! [B_472,C_473] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_472,C_473)) ) ),
    inference(resolution,[status(thm)],[c_10475,c_1336])).

tff(c_10520,plain,(
    ! [B_472,C_473] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_472,C_473)) ),
    inference(splitLeft,[status(thm)],[c_10509])).

tff(c_10342,plain,(
    ! [B_466,C_467] :
      ( r2_hidden('#skF_3'('#skF_5',B_466,C_467),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_466,C_467)) ) ),
    inference(resolution,[status(thm)],[c_8649,c_67])).

tff(c_10376,plain,(
    ! [B_466,C_467] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_466,C_467)) ) ),
    inference(resolution,[status(thm)],[c_10342,c_1336])).

tff(c_10387,plain,(
    ! [B_466,C_467] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_466,C_467)) ),
    inference(splitLeft,[status(thm)],[c_10376])).

tff(c_9986,plain,(
    ! [B_455,C_456] :
      ( r2_hidden('#skF_3'('#skF_5',B_455,C_456),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_455,C_456)) ) ),
    inference(resolution,[status(thm)],[c_9011,c_67])).

tff(c_10020,plain,(
    ! [B_455,C_456] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_455,C_456)) ) ),
    inference(resolution,[status(thm)],[c_9986,c_1336])).

tff(c_10031,plain,(
    ! [B_455,C_456] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_455,C_456)) ),
    inference(splitLeft,[status(thm)],[c_10020])).

tff(c_9419,plain,(
    ! [B_446,C_447] :
      ( r2_hidden('#skF_3'('#skF_5',B_446,C_447),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_446,C_447)) ) ),
    inference(resolution,[status(thm)],[c_7863,c_67])).

tff(c_9453,plain,(
    ! [B_446,C_447] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_446,C_447)) ) ),
    inference(resolution,[status(thm)],[c_9419,c_1336])).

tff(c_9464,plain,(
    ! [B_446,C_447] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_446,C_447)) ),
    inference(splitLeft,[status(thm)],[c_9453])).

tff(c_9302,plain,(
    ! [B_444,C_445] :
      ( r2_hidden('#skF_3'('#skF_5',B_444,C_445),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_444,C_445)) ) ),
    inference(resolution,[status(thm)],[c_8112,c_67])).

tff(c_9336,plain,(
    ! [B_444,C_445] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_444,C_445)) ) ),
    inference(resolution,[status(thm)],[c_9302,c_1336])).

tff(c_9347,plain,(
    ! [B_444,C_445] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_444,C_445)) ),
    inference(splitLeft,[status(thm)],[c_9336])).

tff(c_9176,plain,(
    ! [B_438,C_439] :
      ( r2_hidden('#skF_3'('#skF_5',B_438,C_439),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ) ),
    inference(resolution,[status(thm)],[c_7224,c_67])).

tff(c_9210,plain,(
    ! [B_438,C_439] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ) ),
    inference(resolution,[status(thm)],[c_9176,c_1336])).

tff(c_9221,plain,(
    ! [B_438,C_439] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ),
    inference(splitLeft,[status(thm)],[c_9210])).

tff(c_9275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9221,c_9160])).

tff(c_9276,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9210])).

tff(c_9402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9347,c_9276])).

tff(c_9403,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9336])).

tff(c_9520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9464,c_9403])).

tff(c_9521,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9453])).

tff(c_10088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10031,c_9521])).

tff(c_10089,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10020])).

tff(c_10455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10387,c_10089])).

tff(c_10456,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10376])).

tff(c_10579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10520,c_10456])).

tff(c_10580,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10509])).

tff(c_10860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10790,c_10580])).

tff(c_10861,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10779])).

tff(c_10986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10925,c_10861])).

tff(c_10987,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10914])).

tff(c_11365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11303,c_10987])).

tff(c_11366,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11282])).

tff(c_11655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11430,c_11366])).

tff(c_11656,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11419])).

tff(c_11794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11730,c_11656])).

tff(c_11795,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11709])).

tff(c_12092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11859,c_11795])).

tff(c_12093,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11848])).

tff(c_12731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12665,c_12093])).

tff(c_12732,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_12146])).

tff(c_13017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12799,c_12732])).

tff(c_13018,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_12788])).

tff(c_13160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13092,c_13018])).

tff(c_13161,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_13074])).

tff(c_13473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13228,c_13161])).

tff(c_13474,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_13217])).

tff(c_13676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13605,c_13474])).

tff(c_13677,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13595])).

tff(c_13771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13699,c_13677])).

tff(c_13772,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13596])).

tff(c_14648,plain,(
    ! [B_572,C_573] :
      ( r2_hidden('#skF_3'('#skF_5',B_572,C_573),k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ) ),
    inference(resolution,[status(thm)],[c_13772,c_67])).

tff(c_14683,plain,(
    ! [B_572,C_573] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ) ),
    inference(resolution,[status(thm)],[c_14648,c_3229])).

tff(c_15593,plain,(
    ! [B_572,C_573] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ),
    inference(splitLeft,[status(thm)],[c_14683])).

tff(c_13594,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3265,c_13496])).

tff(c_14944,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_13594])).

tff(c_14685,plain,(
    ! [B_572,C_573] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ) ),
    inference(resolution,[status(thm)],[c_14648,c_1336])).

tff(c_14696,plain,(
    ! [B_572,C_573] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ),
    inference(splitLeft,[status(thm)],[c_14685])).

tff(c_13970,plain,(
    ! [B_563,C_564] :
      ( r2_hidden('#skF_3'('#skF_5',B_563,C_564),k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ) ),
    inference(resolution,[status(thm)],[c_13677,c_67])).

tff(c_14007,plain,(
    ! [B_563,C_564] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ) ),
    inference(resolution,[status(thm)],[c_13970,c_1336])).

tff(c_14018,plain,(
    ! [B_563,C_564] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ),
    inference(splitLeft,[status(thm)],[c_14007])).

tff(c_14625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14018,c_13772])).

tff(c_14626,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_14007])).

tff(c_14770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14696,c_14626])).

tff(c_14771,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_14685])).

tff(c_15019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14944,c_14771])).

tff(c_15020,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13594])).

tff(c_15669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15593,c_15020])).

tff(c_15670,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_14683])).

tff(c_17024,plain,(
    ! [B_619,C_620] :
      ( r2_hidden('#skF_3'('#skF_5',B_619,C_620),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_619,C_620)) ) ),
    inference(resolution,[status(thm)],[c_15670,c_67])).

tff(c_17058,plain,(
    ! [B_619,C_620] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_619,C_620)) ) ),
    inference(resolution,[status(thm)],[c_17024,c_3230])).

tff(c_22927,plain,(
    ! [B_619,C_620] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_619,C_620)) ),
    inference(splitLeft,[status(thm)],[c_17058])).

tff(c_14004,plain,(
    ! [B_563,C_564] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ) ),
    inference(resolution,[status(thm)],[c_13970,c_3230])).

tff(c_15695,plain,(
    ! [B_563,C_564] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ),
    inference(splitLeft,[status(thm)],[c_14004])).

tff(c_15950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15695,c_15670])).

tff(c_15951,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_14004])).

tff(c_16861,plain,(
    ! [B_613,C_614] :
      ( r2_hidden('#skF_3'('#skF_5',B_613,C_614),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_613,C_614)) ) ),
    inference(resolution,[status(thm)],[c_15951,c_67])).

tff(c_16895,plain,(
    ! [B_613,C_614] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_613,C_614)) ) ),
    inference(resolution,[status(thm)],[c_16861,c_3230])).

tff(c_22578,plain,(
    ! [B_613,C_614] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_613,C_614)) ),
    inference(splitLeft,[status(thm)],[c_16895])).

tff(c_14005,plain,(
    ! [B_563,C_564] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ) ),
    inference(resolution,[status(thm)],[c_13970,c_3229])).

tff(c_15976,plain,(
    ! [B_563,C_564] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ),
    inference(splitLeft,[status(thm)],[c_14005])).

tff(c_16061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15976,c_15951])).

tff(c_16062,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_14005])).

tff(c_16531,plain,(
    ! [B_606,C_607] :
      ( r2_hidden('#skF_3'('#skF_5',B_606,C_607),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ) ),
    inference(resolution,[status(thm)],[c_16062,c_67])).

tff(c_16565,plain,(
    ! [B_606,C_607] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ) ),
    inference(resolution,[status(thm)],[c_16531,c_3230])).

tff(c_22454,plain,(
    ! [B_606,C_607] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ),
    inference(splitLeft,[status(thm)],[c_16565])).

tff(c_17059,plain,(
    ! [B_619,C_620] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_619,C_620)) ) ),
    inference(resolution,[status(thm)],[c_17024,c_3229])).

tff(c_21827,plain,(
    ! [B_619,C_620] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_619,C_620)) ),
    inference(splitLeft,[status(thm)],[c_17059])).

tff(c_16566,plain,(
    ! [B_606,C_607] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ) ),
    inference(resolution,[status(thm)],[c_16531,c_3229])).

tff(c_21511,plain,(
    ! [B_606,C_607] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ),
    inference(splitLeft,[status(thm)],[c_16566])).

tff(c_14682,plain,(
    ! [B_572,C_573] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ) ),
    inference(resolution,[status(thm)],[c_14648,c_3230])).

tff(c_16087,plain,(
    ! [B_572,C_573] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ),
    inference(splitLeft,[status(thm)],[c_14682])).

tff(c_16166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16087,c_16062])).

tff(c_16167,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_14682])).

tff(c_17343,plain,(
    ! [B_626,C_627] :
      ( r2_hidden('#skF_3'('#skF_5',B_626,C_627),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_626,C_627)) ) ),
    inference(resolution,[status(thm)],[c_16167,c_67])).

tff(c_17377,plain,(
    ! [B_626,C_627] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_626,C_627)) ) ),
    inference(resolution,[status(thm)],[c_17343,c_3230])).

tff(c_21390,plain,(
    ! [B_626,C_627] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_626,C_627)) ),
    inference(splitLeft,[status(thm)],[c_17377])).

tff(c_16896,plain,(
    ! [B_613,C_614] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_613,C_614)) ) ),
    inference(resolution,[status(thm)],[c_16861,c_3229])).

tff(c_20774,plain,(
    ! [B_613,C_614] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_613,C_614)) ),
    inference(splitLeft,[status(thm)],[c_16896])).

tff(c_17378,plain,(
    ! [B_626,C_627] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_626,C_627)) ) ),
    inference(resolution,[status(thm)],[c_17343,c_3229])).

tff(c_20655,plain,(
    ! [B_626,C_627] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_626,C_627)) ),
    inference(splitLeft,[status(thm)],[c_17378])).

tff(c_3749,plain,(
    ! [A_1,B_293,C_294] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_1,k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_293,C_294),A_1)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_293,C_294)) ) ),
    inference(resolution,[status(thm)],[c_3716,c_1352])).

tff(c_14003,plain,(
    ! [B_563,C_564] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ) ),
    inference(resolution,[status(thm)],[c_13970,c_3749])).

tff(c_20041,plain,(
    ! [B_563,C_564] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_563,C_564)) ),
    inference(splitLeft,[status(thm)],[c_14003])).

tff(c_14681,plain,(
    ! [B_572,C_573] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ) ),
    inference(resolution,[status(thm)],[c_14648,c_3749])).

tff(c_19924,plain,(
    ! [B_572,C_573] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_572,C_573)) ),
    inference(splitLeft,[status(thm)],[c_14681])).

tff(c_16370,plain,(
    ! [B_600,C_601] :
      ( r2_hidden('#skF_3'('#skF_5',B_600,C_601),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_600,C_601)) ) ),
    inference(resolution,[status(thm)],[c_15020,c_67])).

tff(c_16405,plain,(
    ! [B_600,C_601] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_600,C_601)) ) ),
    inference(resolution,[status(thm)],[c_16370,c_3229])).

tff(c_19808,plain,(
    ! [B_600,C_601] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_600,C_601)) ),
    inference(splitLeft,[status(thm)],[c_16405])).

tff(c_16404,plain,(
    ! [B_600,C_601] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_600,C_601)) ) ),
    inference(resolution,[status(thm)],[c_16370,c_3230])).

tff(c_19197,plain,(
    ! [B_600,C_601] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_600,C_601)) ),
    inference(splitLeft,[status(thm)],[c_16404])).

tff(c_3948,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3937,c_67])).

tff(c_13589,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3948,c_13496])).

tff(c_19083,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_13589])).

tff(c_4199,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_4139,c_67])).

tff(c_13588,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_4199,c_13496])).

tff(c_18970,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_13588])).

tff(c_13593,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3472,c_13496])).

tff(c_18362,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_13593])).

tff(c_4117,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3969,c_67])).

tff(c_13590,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_4117,c_13496])).

tff(c_18071,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_13590])).

tff(c_17380,plain,(
    ! [B_626,C_627] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_626,C_627)) ) ),
    inference(resolution,[status(thm)],[c_17343,c_1336])).

tff(c_17391,plain,(
    ! [B_626,C_627] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_626,C_627)) ),
    inference(splitLeft,[status(thm)],[c_17380])).

tff(c_17061,plain,(
    ! [B_619,C_620] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_619,C_620)) ) ),
    inference(resolution,[status(thm)],[c_17024,c_1336])).

tff(c_17072,plain,(
    ! [B_619,C_620] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_619,C_620)) ),
    inference(splitLeft,[status(thm)],[c_17061])).

tff(c_16898,plain,(
    ! [B_613,C_614] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_613,C_614)) ) ),
    inference(resolution,[status(thm)],[c_16861,c_1336])).

tff(c_16909,plain,(
    ! [B_613,C_614] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_613,C_614)) ),
    inference(splitLeft,[status(thm)],[c_16898])).

tff(c_16568,plain,(
    ! [B_606,C_607] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ) ),
    inference(resolution,[status(thm)],[c_16531,c_1336])).

tff(c_16579,plain,(
    ! [B_606,C_607] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ),
    inference(splitLeft,[status(thm)],[c_16568])).

tff(c_16407,plain,(
    ! [B_600,C_601] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_600,C_601)) ) ),
    inference(resolution,[status(thm)],[c_16370,c_1336])).

tff(c_16418,plain,(
    ! [B_600,C_601] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_600,C_601)) ),
    inference(splitLeft,[status(thm)],[c_16407])).

tff(c_16498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16418,c_16167])).

tff(c_16499,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_16407])).

tff(c_16660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16579,c_16499])).

tff(c_16661,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_16568])).

tff(c_16991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16909,c_16661])).

tff(c_16992,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_16898])).

tff(c_17155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17072,c_16992])).

tff(c_17156,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_17061])).

tff(c_17475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17391,c_17156])).

tff(c_17476,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_17380])).

tff(c_18156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18071,c_17476])).

tff(c_18157,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13590])).

tff(c_18448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18362,c_18157])).

tff(c_18449,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13593])).

tff(c_19057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18970,c_18449])).

tff(c_19058,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13588])).

tff(c_19171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19083,c_19058])).

tff(c_19172,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_13589])).

tff(c_19286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19197,c_19172])).

tff(c_19287,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16404])).

tff(c_19898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19808,c_19287])).

tff(c_19899,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16405])).

tff(c_20015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19924,c_19899])).

tff(c_20016,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_14681])).

tff(c_20629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20041,c_20016])).

tff(c_20630,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_14003])).

tff(c_20748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20655,c_20630])).

tff(c_20749,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_17378])).

tff(c_20868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20774,c_20749])).

tff(c_20869,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16896])).

tff(c_21485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21390,c_20869])).

tff(c_21486,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_17377])).

tff(c_21607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21511,c_21486])).

tff(c_21608,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16566])).

tff(c_21924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21827,c_21608])).

tff(c_21925,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_17059])).

tff(c_22552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22454,c_21925])).

tff(c_22553,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16565])).

tff(c_22901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22578,c_22553])).

tff(c_22902,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16895])).

tff(c_23531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22927,c_22902])).

tff(c_23532,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_17058])).

tff(c_30243,plain,(
    ! [B_782,C_783] :
      ( r2_hidden('#skF_3'('#skF_5',B_782,C_783),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_782,C_783)) ) ),
    inference(resolution,[status(thm)],[c_23532,c_67])).

tff(c_30310,plain,(
    ! [B_782,C_783] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_782,C_783)) ) ),
    inference(resolution,[status(thm)],[c_30243,c_1336])).

tff(c_30889,plain,(
    ! [B_782,C_783] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_782,C_783)) ),
    inference(splitLeft,[status(thm)],[c_30310])).

tff(c_30021,plain,(
    ! [B_780,C_781] :
      ( r2_hidden('#skF_3'('#skF_5',B_780,C_781),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_780,C_781)) ) ),
    inference(resolution,[status(thm)],[c_21608,c_67])).

tff(c_30088,plain,(
    ! [B_780,C_781] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_780,C_781)) ) ),
    inference(resolution,[status(thm)],[c_30021,c_1336])).

tff(c_30099,plain,(
    ! [B_780,C_781] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_780,C_781)) ),
    inference(splitLeft,[status(thm)],[c_30088])).

tff(c_29241,plain,(
    ! [B_771,C_772] :
      ( r2_hidden('#skF_3'('#skF_5',B_771,C_772),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ) ),
    inference(resolution,[status(thm)],[c_22902,c_67])).

tff(c_29305,plain,(
    ! [B_771,C_772] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ) ),
    inference(resolution,[status(thm)],[c_29241,c_1336])).

tff(c_29878,plain,(
    ! [B_771,C_772] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ),
    inference(splitLeft,[status(thm)],[c_29305])).

tff(c_29024,plain,(
    ! [B_769,C_770] :
      ( r2_hidden('#skF_3'('#skF_5',B_769,C_770),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_769,C_770)) ) ),
    inference(resolution,[status(thm)],[c_20749,c_67])).

tff(c_29088,plain,(
    ! [B_769,C_770] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_769,C_770)) ) ),
    inference(resolution,[status(thm)],[c_29024,c_1336])).

tff(c_29099,plain,(
    ! [B_769,C_770] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_769,C_770)) ),
    inference(splitLeft,[status(thm)],[c_29088])).

tff(c_28808,plain,(
    ! [B_767,C_768] :
      ( r2_hidden('#skF_3'('#skF_5',B_767,C_768),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_767,C_768)) ) ),
    inference(resolution,[status(thm)],[c_22553,c_67])).

tff(c_28872,plain,(
    ! [B_767,C_768] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_767,C_768)) ) ),
    inference(resolution,[status(thm)],[c_28808,c_1336])).

tff(c_28883,plain,(
    ! [B_767,C_768] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_767,C_768)) ),
    inference(splitLeft,[status(thm)],[c_28872])).

tff(c_28593,plain,(
    ! [B_765,C_766] :
      ( r2_hidden('#skF_3'('#skF_5',B_765,C_766),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_765,C_766)) ) ),
    inference(resolution,[status(thm)],[c_21925,c_67])).

tff(c_28657,plain,(
    ! [B_765,C_766] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_765,C_766)) ) ),
    inference(resolution,[status(thm)],[c_28593,c_1336])).

tff(c_28668,plain,(
    ! [B_765,C_766] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_765,C_766)) ),
    inference(splitLeft,[status(thm)],[c_28657])).

tff(c_28284,plain,(
    ! [B_757,C_758] :
      ( r2_hidden('#skF_3'('#skF_5',B_757,C_758),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_757,C_758)) ) ),
    inference(resolution,[status(thm)],[c_21486,c_67])).

tff(c_28348,plain,(
    ! [B_757,C_758] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_757,C_758)) ) ),
    inference(resolution,[status(thm)],[c_28284,c_1336])).

tff(c_28454,plain,(
    ! [B_757,C_758] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_757,C_758)) ),
    inference(splitLeft,[status(thm)],[c_28348])).

tff(c_28071,plain,(
    ! [B_755,C_756] :
      ( r2_hidden('#skF_3'('#skF_5',B_755,C_756),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_755,C_756)) ) ),
    inference(resolution,[status(thm)],[c_20869,c_67])).

tff(c_28135,plain,(
    ! [B_755,C_756] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_755,C_756)) ) ),
    inference(resolution,[status(thm)],[c_28071,c_1336])).

tff(c_28146,plain,(
    ! [B_755,C_756] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_755,C_756)) ),
    inference(splitLeft,[status(thm)],[c_28135])).

tff(c_27081,plain,(
    ! [B_745,C_746] :
      ( r2_hidden('#skF_3'('#skF_5',B_745,C_746),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_745,C_746)) ) ),
    inference(resolution,[status(thm)],[c_20016,c_67])).

tff(c_27142,plain,(
    ! [B_745,C_746] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_745,C_746)) ) ),
    inference(resolution,[status(thm)],[c_27081,c_1336])).

tff(c_27934,plain,(
    ! [B_745,C_746] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_745,C_746)) ),
    inference(splitLeft,[status(thm)],[c_27142])).

tff(c_26876,plain,(
    ! [B_743,C_744] :
      ( r2_hidden('#skF_3'('#skF_5',B_743,C_744),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_743,C_744)) ) ),
    inference(resolution,[status(thm)],[c_20630,c_67])).

tff(c_26937,plain,(
    ! [B_743,C_744] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_743,C_744)) ) ),
    inference(resolution,[status(thm)],[c_26876,c_1336])).

tff(c_26948,plain,(
    ! [B_743,C_744] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_743,C_744)) ),
    inference(splitLeft,[status(thm)],[c_26937])).

tff(c_26141,plain,(
    ! [B_734,C_735] :
      ( r2_hidden('#skF_3'('#skF_5',B_734,C_735),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_734,C_735)) ) ),
    inference(resolution,[status(thm)],[c_19287,c_67])).

tff(c_26199,plain,(
    ! [B_734,C_735] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_734,C_735)) ) ),
    inference(resolution,[status(thm)],[c_26141,c_1336])).

tff(c_26744,plain,(
    ! [B_734,C_735] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_734,C_735)) ),
    inference(splitLeft,[status(thm)],[c_26199])).

tff(c_25701,plain,(
    ! [B_727,C_728] :
      ( r2_hidden('#skF_3'('#skF_5',B_727,C_728),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_727,C_728)) ) ),
    inference(resolution,[status(thm)],[c_19899,c_67])).

tff(c_25759,plain,(
    ! [B_727,C_728] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_727,C_728)) ) ),
    inference(resolution,[status(thm)],[c_25701,c_1336])).

tff(c_25770,plain,(
    ! [B_727,C_728] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_727,C_728)) ),
    inference(splitLeft,[status(thm)],[c_25759])).

tff(c_24977,plain,(
    ! [B_718,C_719] :
      ( r2_hidden('#skF_3'('#skF_5',B_718,C_719),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_718,C_719)) ) ),
    inference(resolution,[status(thm)],[c_18449,c_67])).

tff(c_25032,plain,(
    ! [B_718,C_719] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_718,C_719)) ) ),
    inference(resolution,[status(thm)],[c_24977,c_1336])).

tff(c_25571,plain,(
    ! [B_718,C_719] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_718,C_719)) ),
    inference(splitLeft,[status(thm)],[c_25032])).

tff(c_24782,plain,(
    ! [B_716,C_717] :
      ( r2_hidden('#skF_3'('#skF_5',B_716,C_717),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_716,C_717)) ) ),
    inference(resolution,[status(thm)],[c_19172,c_67])).

tff(c_24837,plain,(
    ! [B_716,C_717] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_716,C_717)) ) ),
    inference(resolution,[status(thm)],[c_24782,c_1336])).

tff(c_24848,plain,(
    ! [B_716,C_717] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_716,C_717)) ),
    inference(splitLeft,[status(thm)],[c_24837])).

tff(c_24069,plain,(
    ! [B_707,C_708] :
      ( r2_hidden('#skF_3'('#skF_5',B_707,C_708),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_707,C_708)) ) ),
    inference(resolution,[status(thm)],[c_18157,c_67])).

tff(c_24121,plain,(
    ! [B_707,C_708] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_707,C_708)) ) ),
    inference(resolution,[status(thm)],[c_24069,c_1336])).

tff(c_24654,plain,(
    ! [B_707,C_708] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_707,C_708)) ),
    inference(splitLeft,[status(thm)],[c_24121])).

tff(c_23557,plain,(
    ! [B_696,C_697] :
      ( r2_hidden('#skF_3'('#skF_5',B_696,C_697),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_696,C_697)) ) ),
    inference(resolution,[status(thm)],[c_19058,c_67])).

tff(c_23609,plain,(
    ! [B_696,C_697] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_696,C_697)) ) ),
    inference(resolution,[status(thm)],[c_23557,c_1336])).

tff(c_23620,plain,(
    ! [B_696,C_697] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_696,C_697)) ),
    inference(splitLeft,[status(thm)],[c_23609])).

tff(c_23721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23620,c_23532])).

tff(c_23722,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23609])).

tff(c_24756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24654,c_23722])).

tff(c_24757,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24121])).

tff(c_24951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24848,c_24757])).

tff(c_24952,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24837])).

tff(c_25675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25571,c_24952])).

tff(c_25676,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_25032])).

tff(c_26115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25770,c_25676])).

tff(c_26116,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_25759])).

tff(c_26850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26744,c_26116])).

tff(c_26851,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_26199])).

tff(c_27055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26948,c_26851])).

tff(c_27056,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_26937])).

tff(c_28042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27934,c_27056])).

tff(c_28043,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_27142])).

tff(c_28255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28146,c_28043])).

tff(c_28256,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28135])).

tff(c_28564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28454,c_28256])).

tff(c_28565,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28348])).

tff(c_28779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28668,c_28565])).

tff(c_28780,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28657])).

tff(c_28995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28883,c_28780])).

tff(c_28996,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28872])).

tff(c_29212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29099,c_28996])).

tff(c_29213,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_29088])).

tff(c_29992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29878,c_29213])).

tff(c_29993,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_29305])).

tff(c_30214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30099,c_29993])).

tff(c_30215,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_30088])).

tff(c_31005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30889,c_30215])).

tff(c_31006,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_30310])).

tff(c_31593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31205,c_31006])).

tff(c_31594,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31202])).

tff(c_32579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31622,c_31594])).

tff(c_32580,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31203])).

tff(c_33111,plain,(
    ! [B_814,C_815] :
      ( r2_hidden('#skF_3'('#skF_5',B_814,C_815),k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ) ),
    inference(resolution,[status(thm)],[c_32580,c_67])).

tff(c_33184,plain,(
    ! [B_814,C_815] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ) ),
    inference(resolution,[status(thm)],[c_33111,c_1336])).

tff(c_33195,plain,(
    ! [B_814,C_815] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ),
    inference(splitLeft,[status(thm)],[c_33184])).

tff(c_32608,plain,(
    ! [B_807,C_808] :
      ( r2_hidden('#skF_3'('#skF_5',B_807,C_808),k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ) ),
    inference(resolution,[status(thm)],[c_31594,c_67])).

tff(c_32681,plain,(
    ! [B_807,C_808] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ) ),
    inference(resolution,[status(thm)],[c_32608,c_1336])).

tff(c_32692,plain,(
    ! [B_807,C_808] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ),
    inference(splitLeft,[status(thm)],[c_32681])).

tff(c_32812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32692,c_32580])).

tff(c_32813,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_32681])).

tff(c_34172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33195,c_32813])).

tff(c_34173,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_33184])).

tff(c_34323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34201,c_34173])).

tff(c_34324,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31198])).

tff(c_36472,plain,(
    ! [B_848,C_849] :
      ( r2_hidden('#skF_3'('#skF_5',B_848,C_849),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ) ),
    inference(resolution,[status(thm)],[c_34324,c_67])).

tff(c_36544,plain,(
    ! [B_848,C_849] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ) ),
    inference(resolution,[status(thm)],[c_36472,c_3749])).

tff(c_55428,plain,(
    ! [B_848,C_849] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ),
    inference(splitLeft,[status(thm)],[c_36544])).

tff(c_3297,plain,(
    ! [A_1,B_275,C_276] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_1,k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_275,C_276),A_1)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_275,C_276)) ) ),
    inference(resolution,[status(thm)],[c_3267,c_1352])).

tff(c_36532,plain,(
    ! [B_848,C_849] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ) ),
    inference(resolution,[status(thm)],[c_36472,c_3297])).

tff(c_54974,plain,(
    ! [B_848,C_849] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ),
    inference(splitLeft,[status(thm)],[c_36532])).

tff(c_32679,plain,(
    ! [B_807,C_808] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ) ),
    inference(resolution,[status(thm)],[c_32608,c_3229])).

tff(c_34597,plain,(
    ! [B_807,C_808] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ),
    inference(splitLeft,[status(thm)],[c_32679])).

tff(c_34720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34597,c_34324])).

tff(c_34721,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32679])).

tff(c_36965,plain,(
    ! [B_852,C_853] :
      ( r2_hidden('#skF_3'('#skF_5',B_852,C_853),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_852,C_853)) ) ),
    inference(resolution,[status(thm)],[c_34721,c_67])).

tff(c_37039,plain,(
    ! [B_852,C_853] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_852,C_853)) ) ),
    inference(resolution,[status(thm)],[c_36965,c_3229])).

tff(c_45375,plain,(
    ! [B_852,C_853] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_852,C_853)) ),
    inference(splitLeft,[status(thm)],[c_37039])).

tff(c_37038,plain,(
    ! [B_852,C_853] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_852,C_853)) ) ),
    inference(resolution,[status(thm)],[c_36965,c_3230])).

tff(c_44567,plain,(
    ! [B_852,C_853] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_852,C_853)) ),
    inference(splitLeft,[status(thm)],[c_37038])).

tff(c_33182,plain,(
    ! [B_814,C_815] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ) ),
    inference(resolution,[status(thm)],[c_33111,c_3229])).

tff(c_35620,plain,(
    ! [B_814,C_815] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ),
    inference(splitLeft,[status(thm)],[c_33182])).

tff(c_35744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35620,c_34721])).

tff(c_35745,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_33182])).

tff(c_37213,plain,(
    ! [B_854,C_855] :
      ( r2_hidden('#skF_3'('#skF_5',B_854,C_855),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_854,C_855)) ) ),
    inference(resolution,[status(thm)],[c_35745,c_67])).

tff(c_37287,plain,(
    ! [B_854,C_855] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_854,C_855)) ) ),
    inference(resolution,[status(thm)],[c_37213,c_3229])).

tff(c_44187,plain,(
    ! [B_854,C_855] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_854,C_855)) ),
    inference(splitLeft,[status(thm)],[c_37287])).

tff(c_33181,plain,(
    ! [B_814,C_815] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ) ),
    inference(resolution,[status(thm)],[c_33111,c_3230])).

tff(c_36203,plain,(
    ! [B_814,C_815] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ),
    inference(splitLeft,[status(thm)],[c_33181])).

tff(c_32678,plain,(
    ! [B_807,C_808] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ) ),
    inference(resolution,[status(thm)],[c_32608,c_3230])).

tff(c_35776,plain,(
    ! [B_807,C_808] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ),
    inference(splitLeft,[status(thm)],[c_32678])).

tff(c_35901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35776,c_35745])).

tff(c_35902,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32678])).

tff(c_36329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36203,c_35902])).

tff(c_36330,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_33181])).

tff(c_38076,plain,(
    ! [B_863,C_864] :
      ( r2_hidden('#skF_3'('#skF_5',B_863,C_864),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_863,C_864)) ) ),
    inference(resolution,[status(thm)],[c_36330,c_67])).

tff(c_38152,plain,(
    ! [B_863,C_864] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_863,C_864)) ) ),
    inference(resolution,[status(thm)],[c_38076,c_3230])).

tff(c_44006,plain,(
    ! [B_863,C_864] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_863,C_864)) ),
    inference(splitLeft,[status(thm)],[c_38152])).

tff(c_36718,plain,(
    ! [B_850,C_851] :
      ( r2_hidden('#skF_3'('#skF_5',B_850,C_851),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_850,C_851)) ) ),
    inference(resolution,[status(thm)],[c_35902,c_67])).

tff(c_36792,plain,(
    ! [B_850,C_851] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_850,C_851)) ) ),
    inference(resolution,[status(thm)],[c_36718,c_3229])).

tff(c_43826,plain,(
    ! [B_850,C_851] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_850,C_851)) ),
    inference(splitLeft,[status(thm)],[c_36792])).

tff(c_36791,plain,(
    ! [B_850,C_851] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_850,C_851)) ) ),
    inference(resolution,[status(thm)],[c_36718,c_3230])).

tff(c_43647,plain,(
    ! [B_850,C_851] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_850,C_851)) ),
    inference(splitLeft,[status(thm)],[c_36791])).

tff(c_33168,plain,(
    ! [B_814,C_815] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ) ),
    inference(resolution,[status(thm)],[c_33111,c_3297])).

tff(c_43469,plain,(
    ! [B_814,C_815] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ),
    inference(splitLeft,[status(thm)],[c_33168])).

tff(c_33180,plain,(
    ! [B_814,C_815] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ) ),
    inference(resolution,[status(thm)],[c_33111,c_3749])).

tff(c_43292,plain,(
    ! [B_814,C_815] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_814,C_815)) ),
    inference(splitLeft,[status(thm)],[c_33180])).

tff(c_13968,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_13772,c_67])).

tff(c_31169,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_13968,c_31034])).

tff(c_43116,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_31169])).

tff(c_32677,plain,(
    ! [B_807,C_808] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ) ),
    inference(resolution,[status(thm)],[c_32608,c_3749])).

tff(c_42820,plain,(
    ! [B_807,C_808] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ),
    inference(splitLeft,[status(thm)],[c_32677])).

tff(c_13697,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_3'('#skF_5',B_38,C_39),k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_13677,c_67])).

tff(c_31170,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_13697,c_31034])).

tff(c_42517,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_31170])).

tff(c_36546,plain,(
    ! [B_848,C_849] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ) ),
    inference(resolution,[status(thm)],[c_36472,c_3229])).

tff(c_42344,plain,(
    ! [B_848,C_849] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ),
    inference(splitLeft,[status(thm)],[c_36546])).

tff(c_32665,plain,(
    ! [B_807,C_808] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ) ),
    inference(resolution,[status(thm)],[c_32608,c_3297])).

tff(c_41235,plain,(
    ! [B_807,C_808] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_807,C_808)) ),
    inference(splitLeft,[status(thm)],[c_32665])).

tff(c_36545,plain,(
    ! [B_848,C_849] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ) ),
    inference(resolution,[status(thm)],[c_36472,c_3230])).

tff(c_40869,plain,(
    ! [B_848,C_849] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ),
    inference(splitLeft,[status(thm)],[c_36545])).

tff(c_31196,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3948,c_31034])).

tff(c_39771,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_31196])).

tff(c_31197,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_4117,c_31034])).

tff(c_39407,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_31197])).

tff(c_31195,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_4199,c_31034])).

tff(c_39242,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_31195])).

tff(c_31199,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3472,c_31034])).

tff(c_38457,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_31199])).

tff(c_38155,plain,(
    ! [B_863,C_864] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_863,C_864)) ) ),
    inference(resolution,[status(thm)],[c_38076,c_1336])).

tff(c_38166,plain,(
    ! [B_863,C_864] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_863,C_864)) ),
    inference(splitLeft,[status(thm)],[c_38155])).

tff(c_37289,plain,(
    ! [B_854,C_855] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_854,C_855)) ) ),
    inference(resolution,[status(thm)],[c_37213,c_1336])).

tff(c_37300,plain,(
    ! [B_854,C_855] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_854,C_855)) ),
    inference(splitLeft,[status(thm)],[c_37289])).

tff(c_37041,plain,(
    ! [B_852,C_853] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_852,C_853)) ) ),
    inference(resolution,[status(thm)],[c_36965,c_1336])).

tff(c_37052,plain,(
    ! [B_852,C_853] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_852,C_853)) ),
    inference(splitLeft,[status(thm)],[c_37041])).

tff(c_36794,plain,(
    ! [B_850,C_851] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_850,C_851)) ) ),
    inference(resolution,[status(thm)],[c_36718,c_1336])).

tff(c_36805,plain,(
    ! [B_850,C_851] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_850,C_851)) ),
    inference(splitLeft,[status(thm)],[c_36794])).

tff(c_36548,plain,(
    ! [B_848,C_849] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ) ),
    inference(resolution,[status(thm)],[c_36472,c_1336])).

tff(c_36559,plain,(
    ! [B_848,C_849] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_848,C_849)) ),
    inference(splitLeft,[status(thm)],[c_36548])).

tff(c_36686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36559,c_36330])).

tff(c_36687,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_36548])).

tff(c_36933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36805,c_36687])).

tff(c_36934,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_36794])).

tff(c_37181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37052,c_36934])).

tff(c_37182,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_37041])).

tff(c_37430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37300,c_37182])).

tff(c_37431,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_37289])).

tff(c_38297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38166,c_37431])).

tff(c_38298,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_38155])).

tff(c_38589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38457,c_38298])).

tff(c_38590,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31199])).

tff(c_39375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39242,c_38590])).

tff(c_39376,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31195])).

tff(c_39739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39407,c_39376])).

tff(c_39740,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31197])).

tff(c_40837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39771,c_39740])).

tff(c_40838,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31196])).

tff(c_41005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40869,c_40838])).

tff(c_41006,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36545])).

tff(c_41372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41235,c_41006])).

tff(c_41373,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32665])).

tff(c_42482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42344,c_41373])).

tff(c_42483,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36546])).

tff(c_42656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42517,c_42483])).

tff(c_42657,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31170])).

tff(c_42960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42820,c_42657])).

tff(c_42961,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32677])).

tff(c_43257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43116,c_42961])).

tff(c_43258,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_31169])).

tff(c_43434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43292,c_43258])).

tff(c_43435,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_33180])).

tff(c_43612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43469,c_43435])).

tff(c_43613,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_33168])).

tff(c_43791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43647,c_43613])).

tff(c_43792,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36791])).

tff(c_43971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43826,c_43792])).

tff(c_43972,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36792])).

tff(c_44152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44006,c_43972])).

tff(c_44153,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_38152])).

tff(c_44334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44187,c_44153])).

tff(c_44335,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_37287])).

tff(c_44715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44567,c_44335])).

tff(c_44716,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_37038])).

tff(c_45524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45375,c_44716])).

tff(c_45525,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_37039])).

tff(c_54654,plain,(
    ! [B_1054,C_1055] :
      ( r2_hidden('#skF_3'('#skF_5',B_1054,C_1055),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ) ),
    inference(resolution,[status(thm)],[c_45525,c_67])).

tff(c_54745,plain,(
    ! [B_1054,C_1055] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ) ),
    inference(resolution,[status(thm)],[c_54654,c_1336])).

tff(c_54756,plain,(
    ! [B_1054,C_1055] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ),
    inference(splitLeft,[status(thm)],[c_54745])).

tff(c_37286,plain,(
    ! [B_854,C_855] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_854,C_855)) ) ),
    inference(resolution,[status(thm)],[c_37213,c_3230])).

tff(c_45873,plain,(
    ! [B_854,C_855] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_854,C_855)) ),
    inference(splitLeft,[status(thm)],[c_37286])).

tff(c_38153,plain,(
    ! [B_863,C_864] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_863,C_864)) ) ),
    inference(resolution,[status(thm)],[c_38076,c_3229])).

tff(c_45559,plain,(
    ! [B_863,C_864] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_863,C_864)) ),
    inference(splitLeft,[status(thm)],[c_38153])).

tff(c_45838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45559,c_45525])).

tff(c_45839,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_38153])).

tff(c_46649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45873,c_45839])).

tff(c_46650,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_37286])).

tff(c_54088,plain,(
    ! [B_1046,C_1047] :
      ( r2_hidden('#skF_3'('#skF_5',B_1046,C_1047),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1046,C_1047)) ) ),
    inference(resolution,[status(thm)],[c_46650,c_67])).

tff(c_54179,plain,(
    ! [B_1046,C_1047] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1046,C_1047)) ) ),
    inference(resolution,[status(thm)],[c_54088,c_1336])).

tff(c_54190,plain,(
    ! [B_1046,C_1047] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1046,C_1047)) ),
    inference(splitLeft,[status(thm)],[c_54179])).

tff(c_53770,plain,(
    ! [B_1040,C_1041] :
      ( r2_hidden('#skF_3'('#skF_5',B_1040,C_1041),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1040,C_1041)) ) ),
    inference(resolution,[status(thm)],[c_45839,c_67])).

tff(c_53861,plain,(
    ! [B_1040,C_1041] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1040,C_1041)) ) ),
    inference(resolution,[status(thm)],[c_53770,c_1336])).

tff(c_53872,plain,(
    ! [B_1040,C_1041] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1040,C_1041)) ),
    inference(splitLeft,[status(thm)],[c_53861])).

tff(c_53218,plain,(
    ! [B_1032,C_1033] :
      ( r2_hidden('#skF_3'('#skF_5',B_1032,C_1033),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1032,C_1033)) ) ),
    inference(resolution,[status(thm)],[c_44153,c_67])).

tff(c_53309,plain,(
    ! [B_1032,C_1033] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1032,C_1033)) ) ),
    inference(resolution,[status(thm)],[c_53218,c_1336])).

tff(c_53320,plain,(
    ! [B_1032,C_1033] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1032,C_1033)) ),
    inference(splitLeft,[status(thm)],[c_53309])).

tff(c_52902,plain,(
    ! [B_1026,C_1027] :
      ( r2_hidden('#skF_3'('#skF_5',B_1026,C_1027),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1026,C_1027)) ) ),
    inference(resolution,[status(thm)],[c_43792,c_67])).

tff(c_52993,plain,(
    ! [B_1026,C_1027] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1026,C_1027)) ) ),
    inference(resolution,[status(thm)],[c_52902,c_1336])).

tff(c_53004,plain,(
    ! [B_1026,C_1027] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1026,C_1027)) ),
    inference(splitLeft,[status(thm)],[c_52993])).

tff(c_52352,plain,(
    ! [B_1018,C_1019] :
      ( r2_hidden('#skF_3'('#skF_5',B_1018,C_1019),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1018,C_1019)) ) ),
    inference(resolution,[status(thm)],[c_43972,c_67])).

tff(c_52443,plain,(
    ! [B_1018,C_1019] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1018,C_1019)) ) ),
    inference(resolution,[status(thm)],[c_52352,c_1336])).

tff(c_52454,plain,(
    ! [B_1018,C_1019] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1018,C_1019)) ),
    inference(splitLeft,[status(thm)],[c_52443])).

tff(c_52038,plain,(
    ! [B_1012,C_1013] :
      ( r2_hidden('#skF_3'('#skF_5',B_1012,C_1013),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1012,C_1013)) ) ),
    inference(resolution,[status(thm)],[c_44335,c_67])).

tff(c_52129,plain,(
    ! [B_1012,C_1013] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1012,C_1013)) ) ),
    inference(resolution,[status(thm)],[c_52038,c_1336])).

tff(c_52140,plain,(
    ! [B_1012,C_1013] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1012,C_1013)) ),
    inference(splitLeft,[status(thm)],[c_52129])).

tff(c_51616,plain,(
    ! [B_1005,C_1006] :
      ( r2_hidden('#skF_3'('#skF_5',B_1005,C_1006),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1005,C_1006)) ) ),
    inference(resolution,[status(thm)],[c_44716,c_67])).

tff(c_51707,plain,(
    ! [B_1005,C_1006] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1005,C_1006)) ) ),
    inference(resolution,[status(thm)],[c_51616,c_1336])).

tff(c_51718,plain,(
    ! [B_1005,C_1006] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1005,C_1006)) ),
    inference(splitLeft,[status(thm)],[c_51707])).

tff(c_51304,plain,(
    ! [B_999,C_1000] :
      ( r2_hidden('#skF_3'('#skF_5',B_999,C_1000),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_999,C_1000)) ) ),
    inference(resolution,[status(thm)],[c_43258,c_67])).

tff(c_51395,plain,(
    ! [B_999,C_1000] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_999,C_1000)) ) ),
    inference(resolution,[status(thm)],[c_51304,c_1336])).

tff(c_51406,plain,(
    ! [B_999,C_1000] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_999,C_1000)) ),
    inference(splitLeft,[status(thm)],[c_51395])).

tff(c_50884,plain,(
    ! [B_992,C_993] :
      ( r2_hidden('#skF_3'('#skF_5',B_992,C_993),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_992,C_993)) ) ),
    inference(resolution,[status(thm)],[c_42961,c_67])).

tff(c_50975,plain,(
    ! [B_992,C_993] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_992,C_993)) ) ),
    inference(resolution,[status(thm)],[c_50884,c_1336])).

tff(c_50986,plain,(
    ! [B_992,C_993] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_992,C_993)) ),
    inference(splitLeft,[status(thm)],[c_50975])).

tff(c_50574,plain,(
    ! [B_986,C_987] :
      ( r2_hidden('#skF_3'('#skF_5',B_986,C_987),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_986,C_987)) ) ),
    inference(resolution,[status(thm)],[c_41373,c_67])).

tff(c_50665,plain,(
    ! [B_986,C_987] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_986,C_987)) ) ),
    inference(resolution,[status(thm)],[c_50574,c_1336])).

tff(c_50676,plain,(
    ! [B_986,C_987] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_986,C_987)) ),
    inference(splitLeft,[status(thm)],[c_50665])).

tff(c_50156,plain,(
    ! [B_979,C_980] :
      ( r2_hidden('#skF_3'('#skF_5',B_979,C_980),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_979,C_980)) ) ),
    inference(resolution,[status(thm)],[c_43435,c_67])).

tff(c_50247,plain,(
    ! [B_979,C_980] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_979,C_980)) ) ),
    inference(resolution,[status(thm)],[c_50156,c_1336])).

tff(c_50258,plain,(
    ! [B_979,C_980] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_979,C_980)) ),
    inference(splitLeft,[status(thm)],[c_50247])).

tff(c_49848,plain,(
    ! [B_973,C_974] :
      ( r2_hidden('#skF_3'('#skF_5',B_973,C_974),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_973,C_974)) ) ),
    inference(resolution,[status(thm)],[c_42483,c_67])).

tff(c_49939,plain,(
    ! [B_973,C_974] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_973,C_974)) ) ),
    inference(resolution,[status(thm)],[c_49848,c_1336])).

tff(c_49950,plain,(
    ! [B_973,C_974] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_973,C_974)) ),
    inference(splitLeft,[status(thm)],[c_49939])).

tff(c_49432,plain,(
    ! [B_966,C_967] :
      ( r2_hidden('#skF_3'('#skF_5',B_966,C_967),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_966,C_967)) ) ),
    inference(resolution,[status(thm)],[c_41006,c_67])).

tff(c_49523,plain,(
    ! [B_966,C_967] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_966,C_967)) ) ),
    inference(resolution,[status(thm)],[c_49432,c_1336])).

tff(c_49534,plain,(
    ! [B_966,C_967] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_966,C_967)) ),
    inference(splitLeft,[status(thm)],[c_49523])).

tff(c_49126,plain,(
    ! [B_960,C_961] :
      ( r2_hidden('#skF_3'('#skF_5',B_960,C_961),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_960,C_961)) ) ),
    inference(resolution,[status(thm)],[c_42657,c_67])).

tff(c_49217,plain,(
    ! [B_960,C_961] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_960,C_961)) ) ),
    inference(resolution,[status(thm)],[c_49126,c_1336])).

tff(c_49228,plain,(
    ! [B_960,C_961] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_960,C_961)) ),
    inference(splitLeft,[status(thm)],[c_49217])).

tff(c_48833,plain,(
    ! [B_958,C_959] :
      ( r2_hidden('#skF_3'('#skF_5',B_958,C_959),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_958,C_959)) ) ),
    inference(resolution,[status(thm)],[c_43613,c_67])).

tff(c_48924,plain,(
    ! [B_958,C_959] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_958,C_959)) ) ),
    inference(resolution,[status(thm)],[c_48833,c_1336])).

tff(c_48935,plain,(
    ! [B_958,C_959] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_958,C_959)) ),
    inference(splitLeft,[status(thm)],[c_48924])).

tff(c_48529,plain,(
    ! [B_952,C_953] :
      ( r2_hidden('#skF_3'('#skF_5',B_952,C_953),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_952,C_953)) ) ),
    inference(resolution,[status(thm)],[c_38590,c_67])).

tff(c_48620,plain,(
    ! [B_952,C_953] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_952,C_953)) ) ),
    inference(resolution,[status(thm)],[c_48529,c_1336])).

tff(c_48631,plain,(
    ! [B_952,C_953] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_952,C_953)) ),
    inference(splitLeft,[status(thm)],[c_48620])).

tff(c_48017,plain,(
    ! [B_944,C_945] :
      ( r2_hidden('#skF_3'('#skF_5',B_944,C_945),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_944,C_945)) ) ),
    inference(resolution,[status(thm)],[c_39740,c_67])).

tff(c_48105,plain,(
    ! [B_944,C_945] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_944,C_945)) ) ),
    inference(resolution,[status(thm)],[c_48017,c_1336])).

tff(c_48116,plain,(
    ! [B_944,C_945] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_944,C_945)) ),
    inference(splitLeft,[status(thm)],[c_48105])).

tff(c_47099,plain,(
    ! [B_935,C_936] :
      ( r2_hidden('#skF_3'('#skF_5',B_935,C_936),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_935,C_936)) ) ),
    inference(resolution,[status(thm)],[c_39376,c_67])).

tff(c_47187,plain,(
    ! [B_935,C_936] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_935,C_936)) ) ),
    inference(resolution,[status(thm)],[c_47099,c_1336])).

tff(c_47198,plain,(
    ! [B_935,C_936] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_935,C_936)) ),
    inference(splitLeft,[status(thm)],[c_47187])).

tff(c_46684,plain,(
    ! [B_929,C_930] :
      ( r2_hidden('#skF_3'('#skF_5',B_929,C_930),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_929,C_930)) ) ),
    inference(resolution,[status(thm)],[c_40838,c_67])).

tff(c_46772,plain,(
    ! [B_929,C_930] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_929,C_930)) ) ),
    inference(resolution,[status(thm)],[c_46684,c_1336])).

tff(c_46783,plain,(
    ! [B_929,C_930] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_929,C_930)) ),
    inference(splitLeft,[status(thm)],[c_46772])).

tff(c_46935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46783,c_46650])).

tff(c_46936,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_46772])).

tff(c_47982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47198,c_46936])).

tff(c_47983,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_47187])).

tff(c_48270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48116,c_47983])).

tff(c_48271,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_48105])).

tff(c_48798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48631,c_48271])).

tff(c_48799,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_48620])).

tff(c_49091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48935,c_48799])).

tff(c_49092,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_48924])).

tff(c_49397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49228,c_49092])).

tff(c_49398,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_49217])).

tff(c_49692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49534,c_49398])).

tff(c_49693,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_49523])).

tff(c_50121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49950,c_49693])).

tff(c_50122,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_49939])).

tff(c_50418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50258,c_50122])).

tff(c_50419,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_50247])).

tff(c_50849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50676,c_50419])).

tff(c_50850,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_50665])).

tff(c_51148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50986,c_50850])).

tff(c_51149,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_50975])).

tff(c_51581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51406,c_51149])).

tff(c_51582,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_51395])).

tff(c_51882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51718,c_51582])).

tff(c_51883,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_51707])).

tff(c_52317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52140,c_51883])).

tff(c_52318,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_52129])).

tff(c_52620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52454,c_52318])).

tff(c_52621,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_52443])).

tff(c_53183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53004,c_52621])).

tff(c_53184,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_52993])).

tff(c_53488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53320,c_53184])).

tff(c_53489,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_53309])).

tff(c_54053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53872,c_53489])).

tff(c_54054,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_53861])).

tff(c_54360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54190,c_54054])).

tff(c_54361,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_54179])).

tff(c_54939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54756,c_54361])).

tff(c_54940,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_54745])).

tff(c_55146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54974,c_54940])).

tff(c_55147,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36532])).

tff(c_55601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55428,c_55147])).

tff(c_55602,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36544])).

tff(c_55835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55659,c_55602])).

tff(c_55836,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_9','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_55657])).

tff(c_64,plain,(
    ! [C_39,B_38,D_15,A_37,C_14] :
      ( r2_hidden('#skF_4'(A_37,B_38,C_39),D_15)
      | ~ r2_hidden(A_37,k2_zfmisc_1(C_14,D_15))
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_24])).

tff(c_55870,plain,(
    ! [B_1073,C_1074] :
      ( r2_hidden('#skF_4'('#skF_5',B_1073,C_1074),k3_xboole_0('#skF_9','#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1073,C_1074)) ) ),
    inference(resolution,[status(thm)],[c_55836,c_64])).

tff(c_55644,plain,(
    ! [A_1066,B_57,C_59] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1066,'#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_57,C_59),A_1066)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_199,c_55636])).

tff(c_55927,plain,(
    ! [B_1073,C_1074] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1073,C_1074)) ) ),
    inference(resolution,[status(thm)],[c_55870,c_55644])).

tff(c_56201,plain,(
    ! [B_1073,C_1074] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1073,C_1074)) ),
    inference(splitLeft,[status(thm)],[c_55927])).

tff(c_56378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56201,c_55836])).

tff(c_56379,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_55927])).

tff(c_56607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56428,c_56379])).

tff(c_56608,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56424])).

tff(c_56642,plain,(
    ! [B_1084,C_1085] :
      ( r2_hidden('#skF_4'('#skF_5',B_1084,C_1085),k3_xboole_0('#skF_7','#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1084,C_1085)) ) ),
    inference(resolution,[status(thm)],[c_56608,c_64])).

tff(c_61,plain,(
    ! [C_39,B_38,D_15,A_37,C_14] :
      ( r2_hidden(A_37,k2_zfmisc_1(C_14,D_15))
      | ~ r2_hidden('#skF_4'(A_37,B_38,C_39),D_15)
      | ~ r2_hidden('#skF_3'(A_37,B_38,C_39),C_14)
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_22])).

tff(c_68338,plain,(
    ! [C_1238,B_1239,C_1240] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_1238,k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1239,C_1240),C_1238)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1239,C_1240)) ) ),
    inference(resolution,[status(thm)],[c_56642,c_61])).

tff(c_68494,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_3714,c_68338])).

tff(c_68585,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_68494])).

tff(c_55869,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_4'('#skF_5',B_38,C_39),k3_xboole_0('#skF_9','#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_55836,c_64])).

tff(c_56423,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_55869,c_56413])).

tff(c_56729,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_56423])).

tff(c_57164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56729,c_56608])).

tff(c_57165,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56423])).

tff(c_57198,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_4'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57165,c_64])).

tff(c_58166,plain,(
    ! [A_1108,B_1109,B_1110,C_1111] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1108,B_1109)))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1110,C_1111),B_1109)
      | ~ r2_hidden('#skF_4'('#skF_5',B_1110,C_1111),A_1108)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1110,C_1111)) ) ),
    inference(resolution,[status(thm)],[c_252,c_48272])).

tff(c_60866,plain,(
    ! [A_1138,B_1139,C_1140] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1138,'#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1139,C_1140),A_1138)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1139,C_1140)) ) ),
    inference(resolution,[status(thm)],[c_199,c_58166])).

tff(c_60886,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57198,c_60866])).

tff(c_64784,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_60886])).

tff(c_55645,plain,(
    ! [A_1066,B_57,C_59] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1066,'#skF_9')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_57,C_59),A_1066)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_198,c_55636])).

tff(c_56701,plain,(
    ! [B_1084,C_1085] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1084,C_1085)) ) ),
    inference(resolution,[status(thm)],[c_56642,c_55645])).

tff(c_57199,plain,(
    ! [B_1084,C_1085] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1084,C_1085)) ),
    inference(splitLeft,[status(thm)],[c_56701])).

tff(c_57398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57199,c_57165])).

tff(c_57399,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56701])).

tff(c_57432,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_4'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57399,c_64])).

tff(c_60887,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57432,c_60866])).

tff(c_64118,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_60887])).

tff(c_56702,plain,(
    ! [B_1084,C_1085] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1084,C_1085)) ) ),
    inference(resolution,[status(thm)],[c_56642,c_55644])).

tff(c_57433,plain,(
    ! [B_1084,C_1085] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1084,C_1085)) ),
    inference(splitLeft,[status(thm)],[c_56702])).

tff(c_57615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57433,c_57399])).

tff(c_57616,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56702])).

tff(c_57649,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_4'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57616,c_64])).

tff(c_59936,plain,(
    ! [A_1129,B_1130,C_1131] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1129,'#skF_9')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1130,C_1131),A_1129)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1130,C_1131)) ) ),
    inference(resolution,[status(thm)],[c_198,c_58166])).

tff(c_59958,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57649,c_59936])).

tff(c_63815,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_59958])).

tff(c_56412,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_4'('#skF_5',B_38,C_39),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_56379,c_64])).

tff(c_60889,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_56412,c_60866])).

tff(c_63575,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_60889])).

tff(c_59956,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57198,c_59936])).

tff(c_63274,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_59956])).

tff(c_60888,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57649,c_60866])).

tff(c_63037,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_60888])).

tff(c_58192,plain,(
    ! [B_1112,C_1113] :
      ( r2_hidden('#skF_4'('#skF_5',B_1112,C_1113),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1112,C_1113)) ) ),
    inference(resolution,[status(thm)],[c_57165,c_64])).

tff(c_58254,plain,(
    ! [B_1112,C_1113] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1112,C_1113)) ) ),
    inference(resolution,[status(thm)],[c_58192,c_55645])).

tff(c_62792,plain,(
    ! [B_1112,C_1113] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1112,C_1113)) ),
    inference(splitLeft,[status(thm)],[c_58254])).

tff(c_58255,plain,(
    ! [B_1112,C_1113] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1112,C_1113)) ) ),
    inference(resolution,[status(thm)],[c_58192,c_55644])).

tff(c_62494,plain,(
    ! [B_1112,C_1113] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1112,C_1113)) ),
    inference(splitLeft,[status(thm)],[c_58255])).

tff(c_59957,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_57432,c_59936])).

tff(c_62260,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_59957])).

tff(c_57905,plain,(
    ! [B_1102,C_1103] :
      ( r2_hidden('#skF_4'('#skF_5',B_1102,C_1103),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1102,C_1103)) ) ),
    inference(resolution,[status(thm)],[c_56379,c_64])).

tff(c_57965,plain,(
    ! [B_1102,C_1103] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1102,C_1103)) ) ),
    inference(resolution,[status(thm)],[c_57905,c_55644])).

tff(c_62002,plain,(
    ! [B_1102,C_1103] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1102,C_1103)) ),
    inference(splitLeft,[status(thm)],[c_57965])).

tff(c_59959,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_56412,c_59936])).

tff(c_61707,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_59959])).

tff(c_60891,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_55869,c_60866])).

tff(c_61451,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_60891])).

tff(c_56641,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_4'('#skF_5',B_38,C_39),k3_xboole_0('#skF_7','#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_56608,c_64])).

tff(c_60890,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_56641,c_60866])).

tff(c_61158,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_60890])).

tff(c_60894,plain,(
    ! [B_57,C_59] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_9','#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_198,c_60866])).

tff(c_60929,plain,(
    ! [B_57,C_59] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ),
    inference(splitLeft,[status(thm)],[c_60894])).

tff(c_59961,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_55869,c_59936])).

tff(c_60672,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_59961])).

tff(c_59960,plain,(
    ! [B_38,C_39] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_56641,c_59936])).

tff(c_60191,plain,(
    ! [B_38,C_39] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_38,C_39)) ),
    inference(splitLeft,[status(thm)],[c_59960])).

tff(c_59962,plain,(
    ! [B_57,C_59] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ) ),
    inference(resolution,[status(thm)],[c_199,c_59936])).

tff(c_59966,plain,(
    ! [B_57,C_59] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_57,C_59)) ),
    inference(splitLeft,[status(thm)],[c_59962])).

tff(c_57992,plain,(
    ! [B_1104,C_1105] :
      ( r2_hidden('#skF_4'('#skF_5',B_1104,C_1105),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1104,C_1105)) ) ),
    inference(resolution,[status(thm)],[c_57616,c_64])).

tff(c_58051,plain,(
    ! [B_1104,C_1105] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1104,C_1105)) ) ),
    inference(resolution,[status(thm)],[c_57992,c_55645])).

tff(c_59713,plain,(
    ! [B_1104,C_1105] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1104,C_1105)) ),
    inference(splitLeft,[status(thm)],[c_58051])).

tff(c_58052,plain,(
    ! [B_1104,C_1105] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1104,C_1105)) ) ),
    inference(resolution,[status(thm)],[c_57992,c_55644])).

tff(c_59232,plain,(
    ! [B_1104,C_1105] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1104,C_1105)) ),
    inference(splitLeft,[status(thm)],[c_58052])).

tff(c_58079,plain,(
    ! [B_1106,C_1107] :
      ( r2_hidden('#skF_4'('#skF_5',B_1106,C_1107),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1106,C_1107)) ) ),
    inference(resolution,[status(thm)],[c_57399,c_64])).

tff(c_58138,plain,(
    ! [B_1106,C_1107] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1106,C_1107)) ) ),
    inference(resolution,[status(thm)],[c_58079,c_55645])).

tff(c_58980,plain,(
    ! [B_1106,C_1107] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1106,C_1107)) ),
    inference(splitLeft,[status(thm)],[c_58138])).

tff(c_58139,plain,(
    ! [B_1106,C_1107] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1106,C_1107)) ) ),
    inference(resolution,[status(thm)],[c_58079,c_55644])).

tff(c_58501,plain,(
    ! [B_1106,C_1107] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1106,C_1107)) ),
    inference(splitLeft,[status(thm)],[c_58139])).

tff(c_57964,plain,(
    ! [B_1102,C_1103] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1102,C_1103)) ) ),
    inference(resolution,[status(thm)],[c_57905,c_55645])).

tff(c_58282,plain,(
    ! [B_1102,C_1103] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1102,C_1103)) ),
    inference(splitLeft,[status(thm)],[c_57964])).

tff(c_58466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58282,c_57616])).

tff(c_58467,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_57964])).

tff(c_58945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58501,c_58467])).

tff(c_58946,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_58139])).

tff(c_59197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58980,c_58946])).

tff(c_59198,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_58138])).

tff(c_59419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59232,c_59198])).

tff(c_59420,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_58052])).

tff(c_59901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59713,c_59420])).

tff(c_59902,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_58051])).

tff(c_60156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59966,c_59902])).

tff(c_60157,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_59962])).

tff(c_60382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60191,c_60157])).

tff(c_60383,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_59960])).

tff(c_60864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60672,c_60383])).

tff(c_60865,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_59961])).

tff(c_61123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60929,c_60865])).

tff(c_61124,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_9','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_60894])).

tff(c_61416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61158,c_61124])).

tff(c_61417,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_60890])).

tff(c_61672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61451,c_61417])).

tff(c_61673,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_60891])).

tff(c_61904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61707,c_61673])).

tff(c_61905,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_59959])).

tff(c_62200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62002,c_61905])).

tff(c_62201,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_57965])).

tff(c_62459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62260,c_62201])).

tff(c_62460,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_59957])).

tff(c_62694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62494,c_62460])).

tff(c_62695,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_58255])).

tff(c_62993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62792,c_62695])).

tff(c_62994,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_58254])).

tff(c_63239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63037,c_62994])).

tff(c_63240,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_60888])).

tff(c_63540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63274,c_63240])).

tff(c_63541,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_59956])).

tff(c_63780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63575,c_63541])).

tff(c_63781,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_60889])).

tff(c_64020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63815,c_63781])).

tff(c_64021,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_59958])).

tff(c_64324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64118,c_64021])).

tff(c_64325,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_60887])).

tff(c_65054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64784,c_64325])).

tff(c_65055,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_60886])).

tff(c_68801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68585,c_65055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.73/16.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.61/16.44  
% 28.61/16.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.61/16.45  %$ r2_hidden > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 28.61/16.45  
% 28.61/16.45  %Foreground sorts:
% 28.61/16.45  
% 28.61/16.45  
% 28.61/16.45  %Background operators:
% 28.61/16.45  
% 28.61/16.45  
% 28.61/16.45  %Foreground operators:
% 28.61/16.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 28.61/16.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.61/16.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.61/16.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 28.61/16.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 28.61/16.45  tff('#skF_7', type, '#skF_7': $i).
% 28.61/16.45  tff('#skF_5', type, '#skF_5': $i).
% 28.61/16.45  tff('#skF_6', type, '#skF_6': $i).
% 28.61/16.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 28.61/16.45  tff('#skF_9', type, '#skF_9': $i).
% 28.61/16.45  tff('#skF_8', type, '#skF_8': $i).
% 28.61/16.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.61/16.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 28.61/16.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 28.61/16.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.61/16.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 28.61/16.45  
% 28.64/16.51  tff(f_54, negated_conjecture, ~(![A, B, C, D, E]: ((r2_hidden(A, k2_zfmisc_1(B, C)) & r2_hidden(A, k2_zfmisc_1(D, E))) => r2_hidden(A, k2_zfmisc_1(k3_xboole_0(B, D), k3_xboole_0(C, E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_zfmisc_1)).
% 28.64/16.51  tff(f_41, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 28.64/16.51  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 28.64/16.51  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 28.64/16.51  tff(c_28, plain, (~r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_7', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 28.64/16.51  tff(c_32, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 28.64/16.51  tff(c_55, plain, (![A_37, B_38, C_39]: (k4_tarski('#skF_3'(A_37, B_38, C_39), '#skF_4'(A_37, B_38, C_39))=A_37 | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 28.64/16.51  tff(c_26, plain, (![A_12, C_14, B_13, D_15]: (r2_hidden(A_12, C_14) | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.64/16.51  tff(c_219, plain, (![D_70, C_72, B_69, C_71, A_68]: (r2_hidden('#skF_3'(A_68, B_69, C_71), C_72) | ~r2_hidden(A_68, k2_zfmisc_1(C_72, D_70)) | ~r2_hidden(A_68, k2_zfmisc_1(B_69, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_26])).
% 28.64/16.51  tff(c_252, plain, (![B_69, C_71]: (r2_hidden('#skF_3'('#skF_5', B_69, C_71), '#skF_6') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_32, c_219])).
% 28.64/16.51  tff(c_30, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 28.64/16.51  tff(c_251, plain, (![B_69, C_71]: (r2_hidden('#skF_3'('#skF_5', B_69, C_71), '#skF_8') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_30, c_219])).
% 28.64/16.51  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.64/16.51  tff(c_24, plain, (![B_13, D_15, A_12, C_14]: (r2_hidden(B_13, D_15) | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.64/16.51  tff(c_166, plain, (![A_56, B_57, C_60, C_59, D_58]: (r2_hidden('#skF_4'(A_56, B_57, C_59), D_58) | ~r2_hidden(A_56, k2_zfmisc_1(C_60, D_58)) | ~r2_hidden(A_56, k2_zfmisc_1(B_57, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_24])).
% 28.64/16.51  tff(c_199, plain, (![B_57, C_59]: (r2_hidden('#skF_4'('#skF_5', B_57, C_59), '#skF_7') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_32, c_166])).
% 28.64/16.51  tff(c_22, plain, (![A_12, B_13, C_14, D_15]: (r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, D_15)) | ~r2_hidden(B_13, D_15) | ~r2_hidden(A_12, C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.64/16.51  tff(c_1321, plain, (![C_162, D_161, C_163, A_159, B_160]: (r2_hidden(A_159, k2_zfmisc_1(C_163, D_161)) | ~r2_hidden('#skF_4'(A_159, B_160, C_162), D_161) | ~r2_hidden('#skF_3'(A_159, B_160, C_162), C_163) | ~r2_hidden(A_159, k2_zfmisc_1(B_160, C_162)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_22])).
% 28.64/16.51  tff(c_1338, plain, (![C_164, B_165, C_166]: (r2_hidden('#skF_5', k2_zfmisc_1(C_164, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_165, C_166), C_164) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_165, C_166)))), inference(resolution, [status(thm)], [c_199, c_1321])).
% 28.64/16.51  tff(c_3221, plain, (![A_268, B_269, B_270, C_271]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_268, B_269), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_270, C_271)) | ~r2_hidden('#skF_3'('#skF_5', B_270, C_271), B_269) | ~r2_hidden('#skF_3'('#skF_5', B_270, C_271), A_268))), inference(resolution, [status(thm)], [c_2, c_1338])).
% 28.64/16.52  tff(c_3657, plain, (![A_290, B_291, C_292]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_290, '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_291, C_292), A_290) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_291, C_292)))), inference(resolution, [status(thm)], [c_251, c_3221])).
% 28.64/16.52  tff(c_3671, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_252, c_3657])).
% 28.64/16.52  tff(c_3687, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_3671])).
% 28.64/16.52  tff(c_3232, plain, (![A_272, B_273, C_274]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_272, '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_273, C_274), A_272) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_273, C_274)))), inference(resolution, [status(thm)], [c_252, c_3221])).
% 28.64/16.52  tff(c_3242, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_251, c_3232])).
% 28.64/16.52  tff(c_3244, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_3242])).
% 28.64/16.52  tff(c_198, plain, (![B_57, C_59]: (r2_hidden('#skF_4'('#skF_5', B_57, C_59), '#skF_9') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_30, c_166])).
% 28.64/16.52  tff(c_1526, plain, (![C_174, B_175, C_176]: (r2_hidden('#skF_5', k2_zfmisc_1(C_174, '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_175, C_176), C_174) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_175, C_176)))), inference(resolution, [status(thm)], [c_198, c_1321])).
% 28.64/16.52  tff(c_1537, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_252, c_1526])).
% 28.64/16.52  tff(c_1541, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_1537])).
% 28.64/16.52  tff(c_1351, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_251, c_1338])).
% 28.64/16.52  tff(c_1353, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_1351])).
% 28.64/16.52  tff(c_1357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1353, c_30])).
% 28.64/16.52  tff(c_1358, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_1351])).
% 28.64/16.52  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1541, c_1358])).
% 28.64/16.52  tff(c_1548, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', '#skF_9'))), inference(splitRight, [status(thm)], [c_1537])).
% 28.64/16.52  tff(c_3253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3244, c_1548])).
% 28.64/16.52  tff(c_3254, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3242])).
% 28.64/16.52  tff(c_67, plain, (![C_39, B_38, D_15, A_37, C_14]: (r2_hidden('#skF_3'(A_37, B_38, C_39), C_14) | ~r2_hidden(A_37, k2_zfmisc_1(C_14, D_15)) | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_26])).
% 28.64/16.52  tff(c_3267, plain, (![B_275, C_276]: (r2_hidden('#skF_3'('#skF_5', B_275, C_276), k3_xboole_0('#skF_8', '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_275, C_276)))), inference(resolution, [status(thm)], [c_3254, c_67])).
% 28.64/16.52  tff(c_3229, plain, (![A_268, B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_268, '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_69, C_71), A_268) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_252, c_3221])).
% 28.64/16.52  tff(c_3296, plain, (![B_275, C_276]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_275, C_276)))), inference(resolution, [status(thm)], [c_3267, c_3229])).
% 28.64/16.52  tff(c_3433, plain, (![B_275, C_276]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_275, C_276)))), inference(splitLeft, [status(thm)], [c_3296])).
% 28.64/16.52  tff(c_1336, plain, (![C_163, B_57, C_59]: (r2_hidden('#skF_5', k2_zfmisc_1(C_163, '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_57, C_59), C_163) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_198, c_1321])).
% 28.64/16.52  tff(c_3298, plain, (![B_275, C_276]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_275, C_276)))), inference(resolution, [status(thm)], [c_3267, c_1336])).
% 28.64/16.52  tff(c_3309, plain, (![B_275, C_276]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_275, C_276)))), inference(splitLeft, [status(thm)], [c_3298])).
% 28.64/16.52  tff(c_3419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3309, c_3254])).
% 28.64/16.52  tff(c_3420, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_3298])).
% 28.64/16.52  tff(c_3460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3433, c_3420])).
% 28.64/16.52  tff(c_3461, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3296])).
% 28.64/16.52  tff(c_3474, plain, (![B_284, C_285]: (r2_hidden('#skF_3'('#skF_5', B_284, C_285), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_284, C_285)))), inference(resolution, [status(thm)], [c_3461, c_67])).
% 28.64/16.52  tff(c_3503, plain, (![B_284, C_285]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_284, C_285)))), inference(resolution, [status(thm)], [c_3474, c_3229])).
% 28.64/16.52  tff(c_3642, plain, (![B_284, C_285]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_284, C_285)))), inference(splitLeft, [status(thm)], [c_3503])).
% 28.64/16.52  tff(c_3505, plain, (![B_284, C_285]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_284, C_285)))), inference(resolution, [status(thm)], [c_3474, c_1336])).
% 28.64/16.52  tff(c_3516, plain, (![B_284, C_285]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_284, C_285)))), inference(splitLeft, [status(thm)], [c_3505])).
% 28.64/16.52  tff(c_3528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3516, c_3461])).
% 28.64/16.52  tff(c_3529, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_3505])).
% 28.64/16.52  tff(c_3655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3642, c_3529])).
% 28.64/16.52  tff(c_3656, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3503])).
% 28.64/16.52  tff(c_3702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3687, c_3656])).
% 28.64/16.52  tff(c_3703, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3671])).
% 28.64/16.52  tff(c_3714, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0('#skF_6', '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3703, c_67])).
% 28.64/16.52  tff(c_48272, plain, (![A_951, C_946, B_950, A_949, C_947, B_948]: (r2_hidden(A_949, k2_zfmisc_1(C_947, k3_xboole_0(A_951, B_950))) | ~r2_hidden('#skF_3'(A_949, B_948, C_946), C_947) | ~r2_hidden(A_949, k2_zfmisc_1(B_948, C_946)) | ~r2_hidden('#skF_4'(A_949, B_948, C_946), B_950) | ~r2_hidden('#skF_4'(A_949, B_948, C_946), A_951))), inference(resolution, [status(thm)], [c_2, c_1321])).
% 28.64/16.52  tff(c_55636, plain, (![A_1066, B_1067, B_1068, C_1069]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1066, B_1067))) | ~r2_hidden('#skF_4'('#skF_5', B_1068, C_1069), B_1067) | ~r2_hidden('#skF_4'('#skF_5', B_1068, C_1069), A_1066) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1068, C_1069)))), inference(resolution, [status(thm)], [c_251, c_48272])).
% 28.64/16.52  tff(c_56413, plain, (![A_1081, B_1082, C_1083]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1081, '#skF_9'))) | ~r2_hidden('#skF_4'('#skF_5', B_1082, C_1083), A_1081) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1082, C_1083)))), inference(resolution, [status(thm)], [c_198, c_55636])).
% 28.64/16.52  tff(c_56424, plain, (![B_57, C_59]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_199, c_56413])).
% 28.64/16.52  tff(c_56428, plain, (![B_57, C_59]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(splitLeft, [status(thm)], [c_56424])).
% 28.64/16.52  tff(c_55647, plain, (![A_1070, B_1071, C_1072]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1070, '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_5', B_1071, C_1072), A_1070) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1071, C_1072)))), inference(resolution, [status(thm)], [c_199, c_55636])).
% 28.64/16.52  tff(c_55657, plain, (![B_57, C_59]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_9', '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_198, c_55647])).
% 28.64/16.52  tff(c_55659, plain, (![B_57, C_59]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(splitLeft, [status(thm)], [c_55657])).
% 28.64/16.52  tff(c_1352, plain, (![A_1, B_2, B_165, C_166]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_1, B_2), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_165, C_166)) | ~r2_hidden('#skF_3'('#skF_5', B_165, C_166), B_2) | ~r2_hidden('#skF_3'('#skF_5', B_165, C_166), A_1))), inference(resolution, [status(thm)], [c_2, c_1338])).
% 28.64/16.52  tff(c_31034, plain, (![A_791, B_792, C_793]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_791, k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_792, C_793), A_791) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_792, C_793)))), inference(resolution, [status(thm)], [c_3267, c_1352])).
% 28.64/16.52  tff(c_31198, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3714, c_31034])).
% 28.64/16.52  tff(c_34201, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_31198])).
% 28.64/16.52  tff(c_31203, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_251, c_31034])).
% 28.64/16.52  tff(c_31622, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_31203])).
% 28.64/16.52  tff(c_31202, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_252, c_31034])).
% 28.64/16.52  tff(c_31205, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_31202])).
% 28.64/16.52  tff(c_3716, plain, (![B_293, C_294]: (r2_hidden('#skF_3'('#skF_5', B_293, C_294), k3_xboole_0('#skF_6', '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(resolution, [status(thm)], [c_3703, c_67])).
% 28.64/16.52  tff(c_13496, plain, (![A_551, B_552, C_553]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_551, k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_552, C_553), A_551) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_552, C_553)))), inference(resolution, [status(thm)], [c_3716, c_1352])).
% 28.64/16.52  tff(c_13596, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_251, c_13496])).
% 28.64/16.52  tff(c_13699, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_13596])).
% 28.64/16.52  tff(c_13595, plain, (![B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_252, c_13496])).
% 28.64/16.52  tff(c_13605, plain, (![B_69, C_71]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(splitLeft, [status(thm)], [c_13595])).
% 28.64/16.52  tff(c_3265, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0('#skF_8', '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3254, c_67])).
% 28.64/16.52  tff(c_3670, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3265, c_3657])).
% 28.64/16.52  tff(c_3950, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_3670])).
% 28.64/16.52  tff(c_3748, plain, (![B_293, C_294]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(resolution, [status(thm)], [c_3716, c_3229])).
% 28.64/16.52  tff(c_3919, plain, (![B_293, C_294]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(splitLeft, [status(thm)], [c_3748])).
% 28.64/16.52  tff(c_3750, plain, (![B_293, C_294]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(resolution, [status(thm)], [c_3716, c_1336])).
% 28.64/16.52  tff(c_3845, plain, (![B_293, C_294]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(splitLeft, [status(thm)], [c_3750])).
% 28.64/16.52  tff(c_3861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3845, c_3703])).
% 28.64/16.52  tff(c_3862, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_3750])).
% 28.64/16.52  tff(c_3936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3919, c_3862])).
% 28.64/16.52  tff(c_3937, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3748])).
% 28.64/16.52  tff(c_3968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3950, c_3937])).
% 28.64/16.52  tff(c_3969, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3670])).
% 28.64/16.52  tff(c_4201, plain, (![B_316, C_317]: (r2_hidden('#skF_3'('#skF_5', B_316, C_317), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_316, C_317)))), inference(resolution, [status(thm)], [c_3969, c_67])).
% 28.64/16.52  tff(c_4233, plain, (![B_316, C_317]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_316, C_317)))), inference(resolution, [status(thm)], [c_4201, c_3229])).
% 28.64/16.52  tff(c_5071, plain, (![B_316, C_317]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_316, C_317)))), inference(splitLeft, [status(thm)], [c_4233])).
% 28.64/16.52  tff(c_4407, plain, (![B_323, C_324]: (r2_hidden('#skF_3'('#skF_5', B_323, C_324), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_323, C_324)))), inference(resolution, [status(thm)], [c_3937, c_67])).
% 28.64/16.52  tff(c_4439, plain, (![B_323, C_324]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_323, C_324)))), inference(resolution, [status(thm)], [c_4407, c_3229])).
% 28.64/16.52  tff(c_5031, plain, (![B_323, C_324]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_323, C_324)))), inference(splitLeft, [status(thm)], [c_4439])).
% 28.64/16.52  tff(c_3230, plain, (![A_268, B_69, C_71]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_268, '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_69, C_71), A_268) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_69, C_71)))), inference(resolution, [status(thm)], [c_251, c_3221])).
% 28.64/16.52  tff(c_3747, plain, (![B_293, C_294]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(resolution, [status(thm)], [c_3716, c_3230])).
% 28.64/16.52  tff(c_4119, plain, (![B_293, C_294]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(splitLeft, [status(thm)], [c_3747])).
% 28.64/16.52  tff(c_4138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4119, c_3969])).
% 28.64/16.52  tff(c_4139, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3747])).
% 28.64/16.52  tff(c_4487, plain, (![B_325, C_326]: (r2_hidden('#skF_3'('#skF_5', B_325, C_326), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_325, C_326)))), inference(resolution, [status(thm)], [c_4139, c_67])).
% 28.64/16.52  tff(c_4518, plain, (![B_325, C_326]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_325, C_326)))), inference(resolution, [status(thm)], [c_4487, c_3230])).
% 28.64/16.52  tff(c_4840, plain, (![B_325, C_326]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_325, C_326)))), inference(splitLeft, [status(thm)], [c_4518])).
% 28.64/16.52  tff(c_4519, plain, (![B_325, C_326]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_325, C_326)))), inference(resolution, [status(thm)], [c_4487, c_3229])).
% 28.64/16.52  tff(c_4802, plain, (![B_325, C_326]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_325, C_326)))), inference(splitLeft, [status(thm)], [c_4519])).
% 28.64/16.52  tff(c_4232, plain, (![B_316, C_317]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_316, C_317)))), inference(resolution, [status(thm)], [c_4201, c_3230])).
% 28.64/16.52  tff(c_4720, plain, (![B_316, C_317]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_316, C_317)))), inference(splitLeft, [status(thm)], [c_4232])).
% 28.64/16.52  tff(c_4521, plain, (![B_325, C_326]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_325, C_326)))), inference(resolution, [status(thm)], [c_4487, c_1336])).
% 28.64/16.52  tff(c_4532, plain, (![B_325, C_326]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_325, C_326)))), inference(splitLeft, [status(thm)], [c_4521])).
% 28.64/16.52  tff(c_4441, plain, (![B_323, C_324]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_323, C_324)))), inference(resolution, [status(thm)], [c_4407, c_1336])).
% 28.64/16.52  tff(c_4452, plain, (![B_323, C_324]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_323, C_324)))), inference(splitLeft, [status(thm)], [c_4441])).
% 28.64/16.52  tff(c_4235, plain, (![B_316, C_317]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_316, C_317)))), inference(resolution, [status(thm)], [c_4201, c_1336])).
% 28.64/16.52  tff(c_4246, plain, (![B_316, C_317]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_316, C_317)))), inference(splitLeft, [status(thm)], [c_4235])).
% 28.64/16.52  tff(c_4266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4246, c_4139])).
% 28.64/16.52  tff(c_4267, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_4235])).
% 28.64/16.52  tff(c_4473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4452, c_4267])).
% 28.64/16.52  tff(c_4474, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_4441])).
% 28.64/16.52  tff(c_4554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4532, c_4474])).
% 28.64/16.52  tff(c_4555, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_4521])).
% 28.64/16.52  tff(c_4743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4720, c_4555])).
% 28.64/16.52  tff(c_4744, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_4232])).
% 28.64/16.52  tff(c_4826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4802, c_4744])).
% 28.64/16.52  tff(c_4827, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_4519])).
% 28.64/16.52  tff(c_4865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4840, c_4827])).
% 28.64/16.52  tff(c_4866, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_4518])).
% 28.64/16.52  tff(c_5057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5031, c_4866])).
% 28.64/16.52  tff(c_5058, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_4439])).
% 28.64/16.52  tff(c_5098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5071, c_5058])).
% 28.64/16.52  tff(c_5099, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_4233])).
% 28.64/16.52  tff(c_6069, plain, (![B_368, C_369]: (r2_hidden('#skF_3'('#skF_5', B_368, C_369), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_368, C_369)))), inference(resolution, [status(thm)], [c_5099, c_67])).
% 28.64/16.52  tff(c_6100, plain, (![B_368, C_369]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_368, C_369)))), inference(resolution, [status(thm)], [c_6069, c_3230])).
% 28.64/16.52  tff(c_8892, plain, (![B_368, C_369]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_368, C_369)))), inference(splitLeft, [status(thm)], [c_6100])).
% 28.64/16.52  tff(c_6163, plain, (![B_370, C_371]: (r2_hidden('#skF_3'('#skF_5', B_370, C_371), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_370, C_371)))), inference(resolution, [status(thm)], [c_4744, c_67])).
% 28.64/16.52  tff(c_6194, plain, (![B_370, C_371]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_370, C_371)))), inference(resolution, [status(thm)], [c_6163, c_3230])).
% 28.64/16.52  tff(c_8816, plain, (![B_370, C_371]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_370, C_371)))), inference(splitLeft, [status(thm)], [c_6194])).
% 28.64/16.52  tff(c_3472, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3461, c_67])).
% 28.64/16.52  tff(c_3669, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3472, c_3657])).
% 28.64/16.52  tff(c_5112, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_3669])).
% 28.64/16.52  tff(c_5280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5112, c_5099])).
% 28.64/16.52  tff(c_5281, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_3669])).
% 28.64/16.52  tff(c_5839, plain, (![B_361, C_362]: (r2_hidden('#skF_3'('#skF_5', B_361, C_362), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_361, C_362)))), inference(resolution, [status(thm)], [c_5281, c_67])).
% 28.64/16.52  tff(c_5871, plain, (![B_361, C_362]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_361, C_362)))), inference(resolution, [status(thm)], [c_5839, c_3229])).
% 28.64/16.52  tff(c_8600, plain, (![B_361, C_362]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_361, C_362)))), inference(splitLeft, [status(thm)], [c_5871])).
% 28.64/16.52  tff(c_5870, plain, (![B_361, C_362]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_361, C_362)))), inference(resolution, [status(thm)], [c_5839, c_3230])).
% 28.64/16.52  tff(c_8536, plain, (![B_361, C_362]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_361, C_362)))), inference(splitLeft, [status(thm)], [c_5870])).
% 28.64/16.52  tff(c_5337, plain, (![B_348, C_349]: (r2_hidden('#skF_3'('#skF_5', B_348, C_349), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_348, C_349)))), inference(resolution, [status(thm)], [c_4866, c_67])).
% 28.64/16.52  tff(c_5369, plain, (![B_348, C_349]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_348, C_349)))), inference(resolution, [status(thm)], [c_5337, c_3229])).
% 28.64/16.52  tff(c_8065, plain, (![B_348, C_349]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_348, C_349)))), inference(splitLeft, [status(thm)], [c_5369])).
% 28.64/16.52  tff(c_4438, plain, (![B_323, C_324]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_323, C_324)))), inference(resolution, [status(thm)], [c_4407, c_3230])).
% 28.64/16.52  tff(c_5294, plain, (![B_323, C_324]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_323, C_324)))), inference(splitLeft, [status(thm)], [c_4438])).
% 28.64/16.52  tff(c_5323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5294, c_5281])).
% 28.64/16.52  tff(c_5324, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_4438])).
% 28.64/16.52  tff(c_5747, plain, (![B_359, C_360]: (r2_hidden('#skF_3'('#skF_5', B_359, C_360), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_359, C_360)))), inference(resolution, [status(thm)], [c_5324, c_67])).
% 28.64/16.52  tff(c_5778, plain, (![B_359, C_360]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_359, C_360)))), inference(resolution, [status(thm)], [c_5747, c_3230])).
% 28.64/16.52  tff(c_7876, plain, (![B_359, C_360]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_359, C_360)))), inference(splitLeft, [status(thm)], [c_5778])).
% 28.64/16.52  tff(c_6385, plain, (![B_377, C_378]: (r2_hidden('#skF_3'('#skF_5', B_377, C_378), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_377, C_378)))), inference(resolution, [status(thm)], [c_5058, c_67])).
% 28.64/16.52  tff(c_6416, plain, (![B_377, C_378]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_377, C_378)))), inference(resolution, [status(thm)], [c_6385, c_3230])).
% 28.64/16.52  tff(c_7424, plain, (![B_377, C_378]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_377, C_378)))), inference(splitLeft, [status(thm)], [c_6416])).
% 28.64/16.52  tff(c_5566, plain, (![B_355, C_356]: (r2_hidden('#skF_3'('#skF_5', B_355, C_356), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_355, C_356)))), inference(resolution, [status(thm)], [c_3656, c_67])).
% 28.64/16.52  tff(c_5598, plain, (![B_355, C_356]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_355, C_356)))), inference(resolution, [status(thm)], [c_5566, c_3229])).
% 28.64/16.52  tff(c_7237, plain, (![B_355, C_356]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_355, C_356)))), inference(splitLeft, [status(thm)], [c_5598])).
% 28.64/16.52  tff(c_5779, plain, (![B_359, C_360]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_359, C_360)))), inference(resolution, [status(thm)], [c_5747, c_3229])).
% 28.64/16.52  tff(c_7181, plain, (![B_359, C_360]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_359, C_360)))), inference(splitLeft, [status(thm)], [c_5779])).
% 28.64/16.52  tff(c_5368, plain, (![B_348, C_349]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_348, C_349)))), inference(resolution, [status(thm)], [c_5337, c_3230])).
% 28.64/16.52  tff(c_7126, plain, (![B_348, C_349]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_348, C_349)))), inference(splitLeft, [status(thm)], [c_5368])).
% 28.64/16.52  tff(c_5597, plain, (![B_355, C_356]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_355, C_356)))), inference(resolution, [status(thm)], [c_5566, c_3230])).
% 28.64/16.52  tff(c_6858, plain, (![B_355, C_356]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_355, C_356)))), inference(splitLeft, [status(thm)], [c_5597])).
% 28.64/16.52  tff(c_5656, plain, (![B_357, C_358]: (r2_hidden('#skF_3'('#skF_5', B_357, C_358), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_357, C_358)))), inference(resolution, [status(thm)], [c_4827, c_67])).
% 28.64/16.52  tff(c_5688, plain, (![B_357, C_358]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_357, C_358)))), inference(resolution, [status(thm)], [c_5656, c_3229])).
% 28.64/16.52  tff(c_6805, plain, (![B_357, C_358]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_357, C_358)))), inference(splitLeft, [status(thm)], [c_5688])).
% 28.64/16.52  tff(c_6195, plain, (![B_370, C_371]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_370, C_371)))), inference(resolution, [status(thm)], [c_6163, c_3229])).
% 28.64/16.52  tff(c_6601, plain, (![B_370, C_371]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_370, C_371)))), inference(splitLeft, [status(thm)], [c_6195])).
% 28.64/16.52  tff(c_6419, plain, (![B_377, C_378]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_377, C_378)))), inference(resolution, [status(thm)], [c_6385, c_1336])).
% 28.64/16.52  tff(c_6430, plain, (![B_377, C_378]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_377, C_378)))), inference(splitLeft, [status(thm)], [c_6419])).
% 28.64/16.52  tff(c_6197, plain, (![B_370, C_371]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_370, C_371)))), inference(resolution, [status(thm)], [c_6163, c_1336])).
% 28.64/16.52  tff(c_6208, plain, (![B_370, C_371]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_370, C_371)))), inference(splitLeft, [status(thm)], [c_6197])).
% 28.64/16.52  tff(c_6103, plain, (![B_368, C_369]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_368, C_369)))), inference(resolution, [status(thm)], [c_6069, c_1336])).
% 28.64/16.52  tff(c_6114, plain, (![B_368, C_369]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_368, C_369)))), inference(splitLeft, [status(thm)], [c_6103])).
% 28.64/16.52  tff(c_5873, plain, (![B_361, C_362]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_361, C_362)))), inference(resolution, [status(thm)], [c_5839, c_1336])).
% 28.64/16.52  tff(c_5884, plain, (![B_361, C_362]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_361, C_362)))), inference(splitLeft, [status(thm)], [c_5873])).
% 28.64/16.52  tff(c_5781, plain, (![B_359, C_360]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_359, C_360)))), inference(resolution, [status(thm)], [c_5747, c_1336])).
% 28.64/16.52  tff(c_5792, plain, (![B_359, C_360]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_359, C_360)))), inference(splitLeft, [status(thm)], [c_5781])).
% 28.64/16.52  tff(c_5690, plain, (![B_357, C_358]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_357, C_358)))), inference(resolution, [status(thm)], [c_5656, c_1336])).
% 28.64/16.52  tff(c_5701, plain, (![B_357, C_358]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_357, C_358)))), inference(splitLeft, [status(thm)], [c_5690])).
% 28.64/16.52  tff(c_5600, plain, (![B_355, C_356]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_355, C_356)))), inference(resolution, [status(thm)], [c_5566, c_1336])).
% 28.64/16.52  tff(c_5611, plain, (![B_355, C_356]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_355, C_356)))), inference(splitLeft, [status(thm)], [c_5600])).
% 28.64/16.52  tff(c_5371, plain, (![B_348, C_349]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_348, C_349)))), inference(resolution, [status(thm)], [c_5337, c_1336])).
% 28.64/16.52  tff(c_5382, plain, (![B_348, C_349]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_348, C_349)))), inference(splitLeft, [status(thm)], [c_5371])).
% 28.64/16.52  tff(c_5412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5382, c_5324])).
% 28.64/16.52  tff(c_5413, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_5371])).
% 28.64/16.52  tff(c_5642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5611, c_5413])).
% 28.64/16.52  tff(c_5643, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_5600])).
% 28.64/16.52  tff(c_5733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5701, c_5643])).
% 28.64/16.52  tff(c_5734, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_5690])).
% 28.64/16.52  tff(c_5825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5792, c_5734])).
% 28.64/16.52  tff(c_5826, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_5781])).
% 28.64/16.52  tff(c_5918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5884, c_5826])).
% 28.64/16.52  tff(c_5919, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_5873])).
% 28.64/16.52  tff(c_6149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6114, c_5919])).
% 28.64/16.52  tff(c_6150, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6103])).
% 28.64/16.52  tff(c_6244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6208, c_6150])).
% 28.64/16.52  tff(c_6245, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6197])).
% 28.64/16.52  tff(c_6467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6430, c_6245])).
% 28.64/16.52  tff(c_6468, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6419])).
% 28.64/16.52  tff(c_6791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6601, c_6468])).
% 28.64/16.52  tff(c_6792, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6195])).
% 28.64/16.52  tff(c_6844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6805, c_6792])).
% 28.64/16.52  tff(c_6845, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5688])).
% 28.64/16.52  tff(c_6898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6858, c_6845])).
% 28.64/16.52  tff(c_6899, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5597])).
% 28.64/16.52  tff(c_7167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7126, c_6899])).
% 28.64/16.52  tff(c_7168, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5368])).
% 28.64/16.52  tff(c_7223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7181, c_7168])).
% 28.64/16.52  tff(c_7224, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5779])).
% 28.64/16.52  tff(c_7410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7237, c_7224])).
% 28.64/16.52  tff(c_7411, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5598])).
% 28.64/16.52  tff(c_7862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7424, c_7411])).
% 28.64/16.52  tff(c_7863, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6416])).
% 28.64/16.52  tff(c_7921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7876, c_7863])).
% 28.64/16.52  tff(c_7922, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5778])).
% 28.64/16.52  tff(c_8111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8065, c_7922])).
% 28.64/16.52  tff(c_8112, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5369])).
% 28.64/16.52  tff(c_8583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8536, c_8112])).
% 28.64/16.52  tff(c_8584, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5870])).
% 28.64/16.52  tff(c_8648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8600, c_8584])).
% 28.64/16.52  tff(c_8649, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5871])).
% 28.64/16.52  tff(c_8865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8816, c_8649])).
% 28.64/16.52  tff(c_8866, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6194])).
% 28.64/16.52  tff(c_8942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8892, c_8866])).
% 28.64/16.52  tff(c_8943, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6100])).
% 28.64/16.52  tff(c_13183, plain, (![B_544, C_545]: (r2_hidden('#skF_3'('#skF_5', B_544, C_545), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_544, C_545)))), inference(resolution, [status(thm)], [c_8943, c_67])).
% 28.64/16.52  tff(c_13217, plain, (![B_544, C_545]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_544, C_545)))), inference(resolution, [status(thm)], [c_13183, c_1336])).
% 28.64/16.52  tff(c_13228, plain, (![B_544, C_545]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_544, C_545)))), inference(splitLeft, [status(thm)], [c_13217])).
% 28.64/16.52  tff(c_5687, plain, (![B_357, C_358]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_357, C_358)))), inference(resolution, [status(thm)], [c_5656, c_3230])).
% 28.64/16.52  tff(c_9027, plain, (![B_357, C_358]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_357, C_358)))), inference(splitLeft, [status(thm)], [c_5687])).
% 28.64/16.52  tff(c_6101, plain, (![B_368, C_369]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_368, C_369)))), inference(resolution, [status(thm)], [c_6069, c_3229])).
% 28.64/16.52  tff(c_8959, plain, (![B_368, C_369]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_368, C_369)))), inference(splitLeft, [status(thm)], [c_6101])).
% 28.64/16.52  tff(c_9010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8959, c_8943])).
% 28.64/16.52  tff(c_9011, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6101])).
% 28.64/16.52  tff(c_9089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9027, c_9011])).
% 28.64/16.52  tff(c_9090, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_5687])).
% 28.64/16.52  tff(c_13040, plain, (![B_538, C_539]: (r2_hidden('#skF_3'('#skF_5', B_538, C_539), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_538, C_539)))), inference(resolution, [status(thm)], [c_9090, c_67])).
% 28.64/16.52  tff(c_13074, plain, (![B_538, C_539]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_538, C_539)))), inference(resolution, [status(thm)], [c_13040, c_1336])).
% 28.64/16.52  tff(c_13092, plain, (![B_538, C_539]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_538, C_539)))), inference(splitLeft, [status(thm)], [c_13074])).
% 28.64/16.52  tff(c_12754, plain, (![B_531, C_532]: (r2_hidden('#skF_3'('#skF_5', B_531, C_532), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_531, C_532)))), inference(resolution, [status(thm)], [c_8866, c_67])).
% 28.64/16.52  tff(c_12788, plain, (![B_531, C_532]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_531, C_532)))), inference(resolution, [status(thm)], [c_12754, c_1336])).
% 28.64/16.52  tff(c_12799, plain, (![B_531, C_532]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_531, C_532)))), inference(splitLeft, [status(thm)], [c_12788])).
% 28.64/16.52  tff(c_12112, plain, (![B_522, C_523]: (r2_hidden('#skF_3'('#skF_5', B_522, C_523), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_522, C_523)))), inference(resolution, [status(thm)], [c_7922, c_67])).
% 28.64/16.52  tff(c_12146, plain, (![B_522, C_523]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_522, C_523)))), inference(resolution, [status(thm)], [c_12112, c_1336])).
% 28.64/16.52  tff(c_12665, plain, (![B_522, C_523]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_522, C_523)))), inference(splitLeft, [status(thm)], [c_12146])).
% 28.64/16.52  tff(c_11814, plain, (![B_515, C_516]: (r2_hidden('#skF_3'('#skF_5', B_515, C_516), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_515, C_516)))), inference(resolution, [status(thm)], [c_6845, c_67])).
% 28.64/16.52  tff(c_11848, plain, (![B_515, C_516]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_515, C_516)))), inference(resolution, [status(thm)], [c_11814, c_1336])).
% 28.64/16.52  tff(c_11859, plain, (![B_515, C_516]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_515, C_516)))), inference(splitLeft, [status(thm)], [c_11848])).
% 28.64/16.52  tff(c_6417, plain, (![B_377, C_378]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_377, C_378)))), inference(resolution, [status(thm)], [c_6385, c_3229])).
% 28.64/16.52  tff(c_9106, plain, (![B_377, C_378]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_377, C_378)))), inference(splitLeft, [status(thm)], [c_6417])).
% 28.64/16.52  tff(c_9159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9106, c_9090])).
% 28.64/16.52  tff(c_9160, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6417])).
% 28.64/16.52  tff(c_11675, plain, (![B_509, C_510]: (r2_hidden('#skF_3'('#skF_5', B_509, C_510), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_509, C_510)))), inference(resolution, [status(thm)], [c_9160, c_67])).
% 28.64/16.52  tff(c_11709, plain, (![B_509, C_510]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_509, C_510)))), inference(resolution, [status(thm)], [c_11675, c_1336])).
% 28.64/16.52  tff(c_11730, plain, (![B_509, C_510]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_509, C_510)))), inference(splitLeft, [status(thm)], [c_11709])).
% 28.64/16.52  tff(c_11385, plain, (![B_502, C_503]: (r2_hidden('#skF_3'('#skF_5', B_502, C_503), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_502, C_503)))), inference(resolution, [status(thm)], [c_7168, c_67])).
% 28.64/16.52  tff(c_11419, plain, (![B_502, C_503]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_502, C_503)))), inference(resolution, [status(thm)], [c_11385, c_1336])).
% 28.64/16.52  tff(c_11430, plain, (![B_502, C_503]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_502, C_503)))), inference(splitLeft, [status(thm)], [c_11419])).
% 28.64/16.52  tff(c_11248, plain, (![B_496, C_497]: (r2_hidden('#skF_3'('#skF_5', B_496, C_497), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_496, C_497)))), inference(resolution, [status(thm)], [c_8584, c_67])).
% 28.64/16.52  tff(c_11282, plain, (![B_496, C_497]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_496, C_497)))), inference(resolution, [status(thm)], [c_11248, c_1336])).
% 28.64/16.52  tff(c_11303, plain, (![B_496, C_497]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_496, C_497)))), inference(splitLeft, [status(thm)], [c_11282])).
% 28.64/16.52  tff(c_10880, plain, (![B_485, C_486]: (r2_hidden('#skF_3'('#skF_5', B_485, C_486), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_485, C_486)))), inference(resolution, [status(thm)], [c_7411, c_67])).
% 28.64/16.52  tff(c_10914, plain, (![B_485, C_486]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_485, C_486)))), inference(resolution, [status(thm)], [c_10880, c_1336])).
% 28.64/16.52  tff(c_10925, plain, (![B_485, C_486]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_485, C_486)))), inference(splitLeft, [status(thm)], [c_10914])).
% 28.64/16.52  tff(c_10745, plain, (![B_479, C_480]: (r2_hidden('#skF_3'('#skF_5', B_479, C_480), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_479, C_480)))), inference(resolution, [status(thm)], [c_6792, c_67])).
% 28.64/16.52  tff(c_10779, plain, (![B_479, C_480]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_479, C_480)))), inference(resolution, [status(thm)], [c_10745, c_1336])).
% 28.64/16.52  tff(c_10790, plain, (![B_479, C_480]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_479, C_480)))), inference(splitLeft, [status(thm)], [c_10779])).
% 28.64/16.52  tff(c_10475, plain, (![B_472, C_473]: (r2_hidden('#skF_3'('#skF_5', B_472, C_473), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_472, C_473)))), inference(resolution, [status(thm)], [c_6899, c_67])).
% 28.64/16.52  tff(c_10509, plain, (![B_472, C_473]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_472, C_473)))), inference(resolution, [status(thm)], [c_10475, c_1336])).
% 28.64/16.52  tff(c_10520, plain, (![B_472, C_473]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_472, C_473)))), inference(splitLeft, [status(thm)], [c_10509])).
% 28.64/16.52  tff(c_10342, plain, (![B_466, C_467]: (r2_hidden('#skF_3'('#skF_5', B_466, C_467), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_466, C_467)))), inference(resolution, [status(thm)], [c_8649, c_67])).
% 28.64/16.52  tff(c_10376, plain, (![B_466, C_467]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_466, C_467)))), inference(resolution, [status(thm)], [c_10342, c_1336])).
% 28.64/16.52  tff(c_10387, plain, (![B_466, C_467]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_466, C_467)))), inference(splitLeft, [status(thm)], [c_10376])).
% 28.64/16.52  tff(c_9986, plain, (![B_455, C_456]: (r2_hidden('#skF_3'('#skF_5', B_455, C_456), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_455, C_456)))), inference(resolution, [status(thm)], [c_9011, c_67])).
% 28.64/16.52  tff(c_10020, plain, (![B_455, C_456]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_455, C_456)))), inference(resolution, [status(thm)], [c_9986, c_1336])).
% 28.64/16.52  tff(c_10031, plain, (![B_455, C_456]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_455, C_456)))), inference(splitLeft, [status(thm)], [c_10020])).
% 28.64/16.52  tff(c_9419, plain, (![B_446, C_447]: (r2_hidden('#skF_3'('#skF_5', B_446, C_447), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_446, C_447)))), inference(resolution, [status(thm)], [c_7863, c_67])).
% 28.64/16.52  tff(c_9453, plain, (![B_446, C_447]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_446, C_447)))), inference(resolution, [status(thm)], [c_9419, c_1336])).
% 28.64/16.52  tff(c_9464, plain, (![B_446, C_447]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_446, C_447)))), inference(splitLeft, [status(thm)], [c_9453])).
% 28.64/16.52  tff(c_9302, plain, (![B_444, C_445]: (r2_hidden('#skF_3'('#skF_5', B_444, C_445), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_444, C_445)))), inference(resolution, [status(thm)], [c_8112, c_67])).
% 28.64/16.52  tff(c_9336, plain, (![B_444, C_445]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_444, C_445)))), inference(resolution, [status(thm)], [c_9302, c_1336])).
% 28.64/16.52  tff(c_9347, plain, (![B_444, C_445]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_444, C_445)))), inference(splitLeft, [status(thm)], [c_9336])).
% 28.64/16.52  tff(c_9176, plain, (![B_438, C_439]: (r2_hidden('#skF_3'('#skF_5', B_438, C_439), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(resolution, [status(thm)], [c_7224, c_67])).
% 28.64/16.52  tff(c_9210, plain, (![B_438, C_439]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(resolution, [status(thm)], [c_9176, c_1336])).
% 28.64/16.52  tff(c_9221, plain, (![B_438, C_439]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(splitLeft, [status(thm)], [c_9210])).
% 28.64/16.52  tff(c_9275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9221, c_9160])).
% 28.64/16.52  tff(c_9276, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9210])).
% 28.64/16.52  tff(c_9402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9347, c_9276])).
% 28.64/16.52  tff(c_9403, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9336])).
% 28.64/16.52  tff(c_9520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9464, c_9403])).
% 28.64/16.52  tff(c_9521, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9453])).
% 28.64/16.52  tff(c_10088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10031, c_9521])).
% 28.64/16.52  tff(c_10089, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10020])).
% 28.64/16.52  tff(c_10455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10387, c_10089])).
% 28.64/16.52  tff(c_10456, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10376])).
% 28.64/16.52  tff(c_10579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10520, c_10456])).
% 28.64/16.52  tff(c_10580, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10509])).
% 28.64/16.52  tff(c_10860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10790, c_10580])).
% 28.64/16.52  tff(c_10861, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10779])).
% 28.64/16.52  tff(c_10986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10925, c_10861])).
% 28.64/16.52  tff(c_10987, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10914])).
% 28.64/16.52  tff(c_11365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11303, c_10987])).
% 28.64/16.52  tff(c_11366, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_11282])).
% 28.64/16.52  tff(c_11655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11430, c_11366])).
% 28.64/16.52  tff(c_11656, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_11419])).
% 28.64/16.52  tff(c_11794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11730, c_11656])).
% 28.64/16.52  tff(c_11795, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_11709])).
% 28.64/16.52  tff(c_12092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11859, c_11795])).
% 28.64/16.52  tff(c_12093, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_11848])).
% 28.64/16.52  tff(c_12731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12665, c_12093])).
% 28.64/16.52  tff(c_12732, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_12146])).
% 28.64/16.52  tff(c_13017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12799, c_12732])).
% 28.64/16.52  tff(c_13018, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_12788])).
% 28.64/16.52  tff(c_13160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13092, c_13018])).
% 28.64/16.52  tff(c_13161, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_13074])).
% 28.64/16.52  tff(c_13473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13228, c_13161])).
% 28.64/16.52  tff(c_13474, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_13217])).
% 28.64/16.52  tff(c_13676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13605, c_13474])).
% 28.64/16.52  tff(c_13677, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_13595])).
% 28.64/16.52  tff(c_13771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13699, c_13677])).
% 28.64/16.52  tff(c_13772, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_13596])).
% 28.64/16.52  tff(c_14648, plain, (![B_572, C_573]: (r2_hidden('#skF_3'('#skF_5', B_572, C_573), k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(resolution, [status(thm)], [c_13772, c_67])).
% 28.64/16.52  tff(c_14683, plain, (![B_572, C_573]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(resolution, [status(thm)], [c_14648, c_3229])).
% 28.64/16.52  tff(c_15593, plain, (![B_572, C_573]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(splitLeft, [status(thm)], [c_14683])).
% 28.64/16.52  tff(c_13594, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3265, c_13496])).
% 28.64/16.52  tff(c_14944, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_13594])).
% 28.64/16.52  tff(c_14685, plain, (![B_572, C_573]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(resolution, [status(thm)], [c_14648, c_1336])).
% 28.64/16.52  tff(c_14696, plain, (![B_572, C_573]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(splitLeft, [status(thm)], [c_14685])).
% 28.64/16.52  tff(c_13970, plain, (![B_563, C_564]: (r2_hidden('#skF_3'('#skF_5', B_563, C_564), k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(resolution, [status(thm)], [c_13677, c_67])).
% 28.64/16.52  tff(c_14007, plain, (![B_563, C_564]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(resolution, [status(thm)], [c_13970, c_1336])).
% 28.64/16.52  tff(c_14018, plain, (![B_563, C_564]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(splitLeft, [status(thm)], [c_14007])).
% 28.64/16.52  tff(c_14625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14018, c_13772])).
% 28.64/16.52  tff(c_14626, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_14007])).
% 28.64/16.52  tff(c_14770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14696, c_14626])).
% 28.64/16.52  tff(c_14771, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_14685])).
% 28.64/16.52  tff(c_15019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14944, c_14771])).
% 28.64/16.52  tff(c_15020, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_13594])).
% 28.64/16.52  tff(c_15669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15593, c_15020])).
% 28.64/16.52  tff(c_15670, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_14683])).
% 28.64/16.52  tff(c_17024, plain, (![B_619, C_620]: (r2_hidden('#skF_3'('#skF_5', B_619, C_620), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_619, C_620)))), inference(resolution, [status(thm)], [c_15670, c_67])).
% 28.64/16.52  tff(c_17058, plain, (![B_619, C_620]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_619, C_620)))), inference(resolution, [status(thm)], [c_17024, c_3230])).
% 28.64/16.52  tff(c_22927, plain, (![B_619, C_620]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_619, C_620)))), inference(splitLeft, [status(thm)], [c_17058])).
% 28.64/16.52  tff(c_14004, plain, (![B_563, C_564]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(resolution, [status(thm)], [c_13970, c_3230])).
% 28.64/16.52  tff(c_15695, plain, (![B_563, C_564]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(splitLeft, [status(thm)], [c_14004])).
% 28.64/16.52  tff(c_15950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15695, c_15670])).
% 28.64/16.52  tff(c_15951, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_14004])).
% 28.64/16.52  tff(c_16861, plain, (![B_613, C_614]: (r2_hidden('#skF_3'('#skF_5', B_613, C_614), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_613, C_614)))), inference(resolution, [status(thm)], [c_15951, c_67])).
% 28.64/16.52  tff(c_16895, plain, (![B_613, C_614]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_613, C_614)))), inference(resolution, [status(thm)], [c_16861, c_3230])).
% 28.64/16.52  tff(c_22578, plain, (![B_613, C_614]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_613, C_614)))), inference(splitLeft, [status(thm)], [c_16895])).
% 28.64/16.52  tff(c_14005, plain, (![B_563, C_564]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(resolution, [status(thm)], [c_13970, c_3229])).
% 28.64/16.52  tff(c_15976, plain, (![B_563, C_564]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(splitLeft, [status(thm)], [c_14005])).
% 28.64/16.52  tff(c_16061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15976, c_15951])).
% 28.64/16.52  tff(c_16062, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_14005])).
% 28.64/16.52  tff(c_16531, plain, (![B_606, C_607]: (r2_hidden('#skF_3'('#skF_5', B_606, C_607), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(resolution, [status(thm)], [c_16062, c_67])).
% 28.64/16.52  tff(c_16565, plain, (![B_606, C_607]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(resolution, [status(thm)], [c_16531, c_3230])).
% 28.64/16.52  tff(c_22454, plain, (![B_606, C_607]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(splitLeft, [status(thm)], [c_16565])).
% 28.64/16.52  tff(c_17059, plain, (![B_619, C_620]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_619, C_620)))), inference(resolution, [status(thm)], [c_17024, c_3229])).
% 28.64/16.52  tff(c_21827, plain, (![B_619, C_620]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_619, C_620)))), inference(splitLeft, [status(thm)], [c_17059])).
% 28.64/16.52  tff(c_16566, plain, (![B_606, C_607]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(resolution, [status(thm)], [c_16531, c_3229])).
% 28.64/16.52  tff(c_21511, plain, (![B_606, C_607]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(splitLeft, [status(thm)], [c_16566])).
% 28.64/16.52  tff(c_14682, plain, (![B_572, C_573]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(resolution, [status(thm)], [c_14648, c_3230])).
% 28.64/16.52  tff(c_16087, plain, (![B_572, C_573]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(splitLeft, [status(thm)], [c_14682])).
% 28.64/16.52  tff(c_16166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16087, c_16062])).
% 28.64/16.52  tff(c_16167, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_14682])).
% 28.64/16.52  tff(c_17343, plain, (![B_626, C_627]: (r2_hidden('#skF_3'('#skF_5', B_626, C_627), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_626, C_627)))), inference(resolution, [status(thm)], [c_16167, c_67])).
% 28.64/16.52  tff(c_17377, plain, (![B_626, C_627]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_626, C_627)))), inference(resolution, [status(thm)], [c_17343, c_3230])).
% 28.64/16.52  tff(c_21390, plain, (![B_626, C_627]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_626, C_627)))), inference(splitLeft, [status(thm)], [c_17377])).
% 28.64/16.52  tff(c_16896, plain, (![B_613, C_614]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_613, C_614)))), inference(resolution, [status(thm)], [c_16861, c_3229])).
% 28.64/16.52  tff(c_20774, plain, (![B_613, C_614]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_613, C_614)))), inference(splitLeft, [status(thm)], [c_16896])).
% 28.64/16.52  tff(c_17378, plain, (![B_626, C_627]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_626, C_627)))), inference(resolution, [status(thm)], [c_17343, c_3229])).
% 28.64/16.52  tff(c_20655, plain, (![B_626, C_627]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_626, C_627)))), inference(splitLeft, [status(thm)], [c_17378])).
% 28.64/16.52  tff(c_3749, plain, (![A_1, B_293, C_294]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_1, k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_293, C_294), A_1) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_293, C_294)))), inference(resolution, [status(thm)], [c_3716, c_1352])).
% 28.64/16.52  tff(c_14003, plain, (![B_563, C_564]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(resolution, [status(thm)], [c_13970, c_3749])).
% 28.64/16.52  tff(c_20041, plain, (![B_563, C_564]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_563, C_564)))), inference(splitLeft, [status(thm)], [c_14003])).
% 28.64/16.52  tff(c_14681, plain, (![B_572, C_573]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(resolution, [status(thm)], [c_14648, c_3749])).
% 28.64/16.52  tff(c_19924, plain, (![B_572, C_573]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_572, C_573)))), inference(splitLeft, [status(thm)], [c_14681])).
% 28.64/16.52  tff(c_16370, plain, (![B_600, C_601]: (r2_hidden('#skF_3'('#skF_5', B_600, C_601), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_600, C_601)))), inference(resolution, [status(thm)], [c_15020, c_67])).
% 28.64/16.52  tff(c_16405, plain, (![B_600, C_601]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_600, C_601)))), inference(resolution, [status(thm)], [c_16370, c_3229])).
% 28.64/16.52  tff(c_19808, plain, (![B_600, C_601]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_600, C_601)))), inference(splitLeft, [status(thm)], [c_16405])).
% 28.64/16.52  tff(c_16404, plain, (![B_600, C_601]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_600, C_601)))), inference(resolution, [status(thm)], [c_16370, c_3230])).
% 28.64/16.52  tff(c_19197, plain, (![B_600, C_601]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_600, C_601)))), inference(splitLeft, [status(thm)], [c_16404])).
% 28.64/16.52  tff(c_3948, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3937, c_67])).
% 28.64/16.52  tff(c_13589, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3948, c_13496])).
% 28.64/16.52  tff(c_19083, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_13589])).
% 28.64/16.52  tff(c_4199, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_4139, c_67])).
% 28.64/16.52  tff(c_13588, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_4199, c_13496])).
% 28.64/16.52  tff(c_18970, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_13588])).
% 28.64/16.52  tff(c_13593, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3472, c_13496])).
% 28.64/16.52  tff(c_18362, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_13593])).
% 28.64/16.52  tff(c_4117, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3969, c_67])).
% 28.64/16.52  tff(c_13590, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_4117, c_13496])).
% 28.64/16.52  tff(c_18071, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_13590])).
% 28.64/16.52  tff(c_17380, plain, (![B_626, C_627]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_626, C_627)))), inference(resolution, [status(thm)], [c_17343, c_1336])).
% 28.64/16.52  tff(c_17391, plain, (![B_626, C_627]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_626, C_627)))), inference(splitLeft, [status(thm)], [c_17380])).
% 28.64/16.52  tff(c_17061, plain, (![B_619, C_620]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_619, C_620)))), inference(resolution, [status(thm)], [c_17024, c_1336])).
% 28.64/16.52  tff(c_17072, plain, (![B_619, C_620]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_619, C_620)))), inference(splitLeft, [status(thm)], [c_17061])).
% 28.64/16.52  tff(c_16898, plain, (![B_613, C_614]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_613, C_614)))), inference(resolution, [status(thm)], [c_16861, c_1336])).
% 28.64/16.52  tff(c_16909, plain, (![B_613, C_614]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_613, C_614)))), inference(splitLeft, [status(thm)], [c_16898])).
% 28.64/16.52  tff(c_16568, plain, (![B_606, C_607]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(resolution, [status(thm)], [c_16531, c_1336])).
% 28.64/16.52  tff(c_16579, plain, (![B_606, C_607]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(splitLeft, [status(thm)], [c_16568])).
% 28.64/16.52  tff(c_16407, plain, (![B_600, C_601]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_600, C_601)))), inference(resolution, [status(thm)], [c_16370, c_1336])).
% 28.64/16.52  tff(c_16418, plain, (![B_600, C_601]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_600, C_601)))), inference(splitLeft, [status(thm)], [c_16407])).
% 28.64/16.52  tff(c_16498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16418, c_16167])).
% 28.64/16.52  tff(c_16499, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_16407])).
% 28.64/16.52  tff(c_16660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16579, c_16499])).
% 28.64/16.52  tff(c_16661, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_16568])).
% 28.64/16.52  tff(c_16991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16909, c_16661])).
% 28.64/16.52  tff(c_16992, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_16898])).
% 28.64/16.52  tff(c_17155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17072, c_16992])).
% 28.64/16.52  tff(c_17156, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_17061])).
% 28.64/16.52  tff(c_17475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17391, c_17156])).
% 28.64/16.52  tff(c_17476, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_17380])).
% 28.64/16.52  tff(c_18156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18071, c_17476])).
% 28.64/16.52  tff(c_18157, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_13590])).
% 28.64/16.52  tff(c_18448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18362, c_18157])).
% 28.64/16.52  tff(c_18449, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_13593])).
% 28.64/16.52  tff(c_19057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18970, c_18449])).
% 28.64/16.52  tff(c_19058, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_13588])).
% 28.64/16.52  tff(c_19171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19083, c_19058])).
% 28.64/16.52  tff(c_19172, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_13589])).
% 28.64/16.52  tff(c_19286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19197, c_19172])).
% 28.64/16.52  tff(c_19287, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_16404])).
% 28.64/16.52  tff(c_19898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19808, c_19287])).
% 28.64/16.52  tff(c_19899, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_16405])).
% 28.64/16.52  tff(c_20015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19924, c_19899])).
% 28.64/16.52  tff(c_20016, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_14681])).
% 28.64/16.52  tff(c_20629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20041, c_20016])).
% 28.64/16.52  tff(c_20630, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_14003])).
% 28.64/16.52  tff(c_20748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20655, c_20630])).
% 28.64/16.52  tff(c_20749, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_17378])).
% 28.64/16.52  tff(c_20868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20774, c_20749])).
% 28.64/16.52  tff(c_20869, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_16896])).
% 28.64/16.52  tff(c_21485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21390, c_20869])).
% 28.64/16.52  tff(c_21486, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_17377])).
% 28.64/16.52  tff(c_21607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21511, c_21486])).
% 28.64/16.52  tff(c_21608, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_16566])).
% 28.64/16.52  tff(c_21924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21827, c_21608])).
% 28.64/16.52  tff(c_21925, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_17059])).
% 28.64/16.52  tff(c_22552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22454, c_21925])).
% 28.64/16.52  tff(c_22553, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_16565])).
% 28.64/16.52  tff(c_22901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22578, c_22553])).
% 28.64/16.52  tff(c_22902, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_16895])).
% 28.64/16.52  tff(c_23531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22927, c_22902])).
% 28.64/16.52  tff(c_23532, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_17058])).
% 28.64/16.52  tff(c_30243, plain, (![B_782, C_783]: (r2_hidden('#skF_3'('#skF_5', B_782, C_783), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_782, C_783)))), inference(resolution, [status(thm)], [c_23532, c_67])).
% 28.64/16.52  tff(c_30310, plain, (![B_782, C_783]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_782, C_783)))), inference(resolution, [status(thm)], [c_30243, c_1336])).
% 28.64/16.52  tff(c_30889, plain, (![B_782, C_783]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_782, C_783)))), inference(splitLeft, [status(thm)], [c_30310])).
% 28.64/16.52  tff(c_30021, plain, (![B_780, C_781]: (r2_hidden('#skF_3'('#skF_5', B_780, C_781), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_780, C_781)))), inference(resolution, [status(thm)], [c_21608, c_67])).
% 28.64/16.52  tff(c_30088, plain, (![B_780, C_781]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_780, C_781)))), inference(resolution, [status(thm)], [c_30021, c_1336])).
% 28.64/16.52  tff(c_30099, plain, (![B_780, C_781]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_780, C_781)))), inference(splitLeft, [status(thm)], [c_30088])).
% 28.64/16.52  tff(c_29241, plain, (![B_771, C_772]: (r2_hidden('#skF_3'('#skF_5', B_771, C_772), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(resolution, [status(thm)], [c_22902, c_67])).
% 28.64/16.52  tff(c_29305, plain, (![B_771, C_772]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(resolution, [status(thm)], [c_29241, c_1336])).
% 28.64/16.52  tff(c_29878, plain, (![B_771, C_772]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(splitLeft, [status(thm)], [c_29305])).
% 28.64/16.52  tff(c_29024, plain, (![B_769, C_770]: (r2_hidden('#skF_3'('#skF_5', B_769, C_770), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_769, C_770)))), inference(resolution, [status(thm)], [c_20749, c_67])).
% 28.64/16.52  tff(c_29088, plain, (![B_769, C_770]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_769, C_770)))), inference(resolution, [status(thm)], [c_29024, c_1336])).
% 28.64/16.52  tff(c_29099, plain, (![B_769, C_770]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_769, C_770)))), inference(splitLeft, [status(thm)], [c_29088])).
% 28.64/16.52  tff(c_28808, plain, (![B_767, C_768]: (r2_hidden('#skF_3'('#skF_5', B_767, C_768), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_767, C_768)))), inference(resolution, [status(thm)], [c_22553, c_67])).
% 28.64/16.52  tff(c_28872, plain, (![B_767, C_768]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_767, C_768)))), inference(resolution, [status(thm)], [c_28808, c_1336])).
% 28.64/16.52  tff(c_28883, plain, (![B_767, C_768]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_767, C_768)))), inference(splitLeft, [status(thm)], [c_28872])).
% 28.64/16.52  tff(c_28593, plain, (![B_765, C_766]: (r2_hidden('#skF_3'('#skF_5', B_765, C_766), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_765, C_766)))), inference(resolution, [status(thm)], [c_21925, c_67])).
% 28.64/16.52  tff(c_28657, plain, (![B_765, C_766]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_765, C_766)))), inference(resolution, [status(thm)], [c_28593, c_1336])).
% 28.64/16.52  tff(c_28668, plain, (![B_765, C_766]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_765, C_766)))), inference(splitLeft, [status(thm)], [c_28657])).
% 28.64/16.52  tff(c_28284, plain, (![B_757, C_758]: (r2_hidden('#skF_3'('#skF_5', B_757, C_758), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_757, C_758)))), inference(resolution, [status(thm)], [c_21486, c_67])).
% 28.64/16.52  tff(c_28348, plain, (![B_757, C_758]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_757, C_758)))), inference(resolution, [status(thm)], [c_28284, c_1336])).
% 28.64/16.52  tff(c_28454, plain, (![B_757, C_758]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_757, C_758)))), inference(splitLeft, [status(thm)], [c_28348])).
% 28.64/16.52  tff(c_28071, plain, (![B_755, C_756]: (r2_hidden('#skF_3'('#skF_5', B_755, C_756), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_755, C_756)))), inference(resolution, [status(thm)], [c_20869, c_67])).
% 28.64/16.52  tff(c_28135, plain, (![B_755, C_756]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_755, C_756)))), inference(resolution, [status(thm)], [c_28071, c_1336])).
% 28.64/16.52  tff(c_28146, plain, (![B_755, C_756]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_755, C_756)))), inference(splitLeft, [status(thm)], [c_28135])).
% 28.64/16.52  tff(c_27081, plain, (![B_745, C_746]: (r2_hidden('#skF_3'('#skF_5', B_745, C_746), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_745, C_746)))), inference(resolution, [status(thm)], [c_20016, c_67])).
% 28.64/16.52  tff(c_27142, plain, (![B_745, C_746]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_745, C_746)))), inference(resolution, [status(thm)], [c_27081, c_1336])).
% 28.64/16.52  tff(c_27934, plain, (![B_745, C_746]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_745, C_746)))), inference(splitLeft, [status(thm)], [c_27142])).
% 28.64/16.52  tff(c_26876, plain, (![B_743, C_744]: (r2_hidden('#skF_3'('#skF_5', B_743, C_744), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_743, C_744)))), inference(resolution, [status(thm)], [c_20630, c_67])).
% 28.64/16.52  tff(c_26937, plain, (![B_743, C_744]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_743, C_744)))), inference(resolution, [status(thm)], [c_26876, c_1336])).
% 28.64/16.52  tff(c_26948, plain, (![B_743, C_744]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_743, C_744)))), inference(splitLeft, [status(thm)], [c_26937])).
% 28.64/16.52  tff(c_26141, plain, (![B_734, C_735]: (r2_hidden('#skF_3'('#skF_5', B_734, C_735), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_734, C_735)))), inference(resolution, [status(thm)], [c_19287, c_67])).
% 28.64/16.52  tff(c_26199, plain, (![B_734, C_735]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_734, C_735)))), inference(resolution, [status(thm)], [c_26141, c_1336])).
% 28.64/16.52  tff(c_26744, plain, (![B_734, C_735]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_734, C_735)))), inference(splitLeft, [status(thm)], [c_26199])).
% 28.64/16.52  tff(c_25701, plain, (![B_727, C_728]: (r2_hidden('#skF_3'('#skF_5', B_727, C_728), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_727, C_728)))), inference(resolution, [status(thm)], [c_19899, c_67])).
% 28.64/16.52  tff(c_25759, plain, (![B_727, C_728]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_727, C_728)))), inference(resolution, [status(thm)], [c_25701, c_1336])).
% 28.64/16.52  tff(c_25770, plain, (![B_727, C_728]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_727, C_728)))), inference(splitLeft, [status(thm)], [c_25759])).
% 28.64/16.52  tff(c_24977, plain, (![B_718, C_719]: (r2_hidden('#skF_3'('#skF_5', B_718, C_719), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_718, C_719)))), inference(resolution, [status(thm)], [c_18449, c_67])).
% 28.64/16.52  tff(c_25032, plain, (![B_718, C_719]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_718, C_719)))), inference(resolution, [status(thm)], [c_24977, c_1336])).
% 28.64/16.52  tff(c_25571, plain, (![B_718, C_719]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_718, C_719)))), inference(splitLeft, [status(thm)], [c_25032])).
% 28.64/16.52  tff(c_24782, plain, (![B_716, C_717]: (r2_hidden('#skF_3'('#skF_5', B_716, C_717), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_716, C_717)))), inference(resolution, [status(thm)], [c_19172, c_67])).
% 28.64/16.52  tff(c_24837, plain, (![B_716, C_717]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_716, C_717)))), inference(resolution, [status(thm)], [c_24782, c_1336])).
% 28.64/16.52  tff(c_24848, plain, (![B_716, C_717]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_716, C_717)))), inference(splitLeft, [status(thm)], [c_24837])).
% 28.64/16.52  tff(c_24069, plain, (![B_707, C_708]: (r2_hidden('#skF_3'('#skF_5', B_707, C_708), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_707, C_708)))), inference(resolution, [status(thm)], [c_18157, c_67])).
% 28.64/16.52  tff(c_24121, plain, (![B_707, C_708]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_707, C_708)))), inference(resolution, [status(thm)], [c_24069, c_1336])).
% 28.64/16.52  tff(c_24654, plain, (![B_707, C_708]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_707, C_708)))), inference(splitLeft, [status(thm)], [c_24121])).
% 28.64/16.52  tff(c_23557, plain, (![B_696, C_697]: (r2_hidden('#skF_3'('#skF_5', B_696, C_697), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_696, C_697)))), inference(resolution, [status(thm)], [c_19058, c_67])).
% 28.64/16.52  tff(c_23609, plain, (![B_696, C_697]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_696, C_697)))), inference(resolution, [status(thm)], [c_23557, c_1336])).
% 28.64/16.52  tff(c_23620, plain, (![B_696, C_697]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_696, C_697)))), inference(splitLeft, [status(thm)], [c_23609])).
% 28.64/16.52  tff(c_23721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23620, c_23532])).
% 28.64/16.52  tff(c_23722, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23609])).
% 28.64/16.52  tff(c_24756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24654, c_23722])).
% 28.64/16.52  tff(c_24757, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_24121])).
% 28.64/16.52  tff(c_24951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24848, c_24757])).
% 28.64/16.52  tff(c_24952, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_24837])).
% 28.64/16.52  tff(c_25675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25571, c_24952])).
% 28.64/16.52  tff(c_25676, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_25032])).
% 28.64/16.52  tff(c_26115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25770, c_25676])).
% 28.64/16.52  tff(c_26116, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_25759])).
% 28.64/16.52  tff(c_26850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26744, c_26116])).
% 28.64/16.52  tff(c_26851, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_26199])).
% 28.64/16.52  tff(c_27055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26948, c_26851])).
% 28.64/16.52  tff(c_27056, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_26937])).
% 28.64/16.52  tff(c_28042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27934, c_27056])).
% 28.64/16.52  tff(c_28043, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_27142])).
% 28.64/16.52  tff(c_28255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28146, c_28043])).
% 28.64/16.52  tff(c_28256, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28135])).
% 28.64/16.52  tff(c_28564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28454, c_28256])).
% 28.64/16.52  tff(c_28565, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28348])).
% 28.64/16.52  tff(c_28779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28668, c_28565])).
% 28.64/16.52  tff(c_28780, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28657])).
% 28.64/16.52  tff(c_28995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28883, c_28780])).
% 28.64/16.52  tff(c_28996, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28872])).
% 28.64/16.52  tff(c_29212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29099, c_28996])).
% 28.64/16.52  tff(c_29213, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_29088])).
% 28.64/16.52  tff(c_29992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29878, c_29213])).
% 28.64/16.52  tff(c_29993, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_29305])).
% 28.64/16.52  tff(c_30214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30099, c_29993])).
% 28.64/16.52  tff(c_30215, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_30088])).
% 28.64/16.52  tff(c_31005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30889, c_30215])).
% 28.64/16.52  tff(c_31006, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_30310])).
% 28.64/16.52  tff(c_31593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31205, c_31006])).
% 28.64/16.52  tff(c_31594, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31202])).
% 28.64/16.52  tff(c_32579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31622, c_31594])).
% 28.64/16.52  tff(c_32580, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31203])).
% 28.64/16.52  tff(c_33111, plain, (![B_814, C_815]: (r2_hidden('#skF_3'('#skF_5', B_814, C_815), k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(resolution, [status(thm)], [c_32580, c_67])).
% 28.64/16.52  tff(c_33184, plain, (![B_814, C_815]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(resolution, [status(thm)], [c_33111, c_1336])).
% 28.64/16.52  tff(c_33195, plain, (![B_814, C_815]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(splitLeft, [status(thm)], [c_33184])).
% 28.64/16.52  tff(c_32608, plain, (![B_807, C_808]: (r2_hidden('#skF_3'('#skF_5', B_807, C_808), k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(resolution, [status(thm)], [c_31594, c_67])).
% 28.64/16.52  tff(c_32681, plain, (![B_807, C_808]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(resolution, [status(thm)], [c_32608, c_1336])).
% 28.64/16.52  tff(c_32692, plain, (![B_807, C_808]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(splitLeft, [status(thm)], [c_32681])).
% 28.64/16.52  tff(c_32812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32692, c_32580])).
% 28.64/16.52  tff(c_32813, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_32681])).
% 28.64/16.52  tff(c_34172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33195, c_32813])).
% 28.64/16.52  tff(c_34173, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_33184])).
% 28.64/16.52  tff(c_34323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34201, c_34173])).
% 28.64/16.52  tff(c_34324, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31198])).
% 28.64/16.52  tff(c_36472, plain, (![B_848, C_849]: (r2_hidden('#skF_3'('#skF_5', B_848, C_849), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(resolution, [status(thm)], [c_34324, c_67])).
% 28.64/16.52  tff(c_36544, plain, (![B_848, C_849]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(resolution, [status(thm)], [c_36472, c_3749])).
% 28.64/16.52  tff(c_55428, plain, (![B_848, C_849]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(splitLeft, [status(thm)], [c_36544])).
% 28.64/16.52  tff(c_3297, plain, (![A_1, B_275, C_276]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_1, k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_275, C_276), A_1) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_275, C_276)))), inference(resolution, [status(thm)], [c_3267, c_1352])).
% 28.64/16.52  tff(c_36532, plain, (![B_848, C_849]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(resolution, [status(thm)], [c_36472, c_3297])).
% 28.64/16.52  tff(c_54974, plain, (![B_848, C_849]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(splitLeft, [status(thm)], [c_36532])).
% 28.64/16.52  tff(c_32679, plain, (![B_807, C_808]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(resolution, [status(thm)], [c_32608, c_3229])).
% 28.64/16.52  tff(c_34597, plain, (![B_807, C_808]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(splitLeft, [status(thm)], [c_32679])).
% 28.64/16.52  tff(c_34720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34597, c_34324])).
% 28.64/16.52  tff(c_34721, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_32679])).
% 28.64/16.52  tff(c_36965, plain, (![B_852, C_853]: (r2_hidden('#skF_3'('#skF_5', B_852, C_853), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_852, C_853)))), inference(resolution, [status(thm)], [c_34721, c_67])).
% 28.64/16.52  tff(c_37039, plain, (![B_852, C_853]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_852, C_853)))), inference(resolution, [status(thm)], [c_36965, c_3229])).
% 28.64/16.52  tff(c_45375, plain, (![B_852, C_853]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_852, C_853)))), inference(splitLeft, [status(thm)], [c_37039])).
% 28.64/16.52  tff(c_37038, plain, (![B_852, C_853]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_852, C_853)))), inference(resolution, [status(thm)], [c_36965, c_3230])).
% 28.64/16.52  tff(c_44567, plain, (![B_852, C_853]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_852, C_853)))), inference(splitLeft, [status(thm)], [c_37038])).
% 28.64/16.52  tff(c_33182, plain, (![B_814, C_815]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(resolution, [status(thm)], [c_33111, c_3229])).
% 28.64/16.52  tff(c_35620, plain, (![B_814, C_815]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(splitLeft, [status(thm)], [c_33182])).
% 28.64/16.52  tff(c_35744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35620, c_34721])).
% 28.64/16.52  tff(c_35745, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_33182])).
% 28.64/16.52  tff(c_37213, plain, (![B_854, C_855]: (r2_hidden('#skF_3'('#skF_5', B_854, C_855), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_854, C_855)))), inference(resolution, [status(thm)], [c_35745, c_67])).
% 28.64/16.52  tff(c_37287, plain, (![B_854, C_855]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_854, C_855)))), inference(resolution, [status(thm)], [c_37213, c_3229])).
% 28.64/16.52  tff(c_44187, plain, (![B_854, C_855]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_854, C_855)))), inference(splitLeft, [status(thm)], [c_37287])).
% 28.64/16.52  tff(c_33181, plain, (![B_814, C_815]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(resolution, [status(thm)], [c_33111, c_3230])).
% 28.64/16.52  tff(c_36203, plain, (![B_814, C_815]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(splitLeft, [status(thm)], [c_33181])).
% 28.64/16.52  tff(c_32678, plain, (![B_807, C_808]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(resolution, [status(thm)], [c_32608, c_3230])).
% 28.64/16.52  tff(c_35776, plain, (![B_807, C_808]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(splitLeft, [status(thm)], [c_32678])).
% 28.64/16.52  tff(c_35901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35776, c_35745])).
% 28.64/16.52  tff(c_35902, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_32678])).
% 28.64/16.52  tff(c_36329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36203, c_35902])).
% 28.64/16.52  tff(c_36330, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_33181])).
% 28.64/16.52  tff(c_38076, plain, (![B_863, C_864]: (r2_hidden('#skF_3'('#skF_5', B_863, C_864), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_863, C_864)))), inference(resolution, [status(thm)], [c_36330, c_67])).
% 28.64/16.52  tff(c_38152, plain, (![B_863, C_864]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_863, C_864)))), inference(resolution, [status(thm)], [c_38076, c_3230])).
% 28.64/16.52  tff(c_44006, plain, (![B_863, C_864]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_863, C_864)))), inference(splitLeft, [status(thm)], [c_38152])).
% 28.64/16.52  tff(c_36718, plain, (![B_850, C_851]: (r2_hidden('#skF_3'('#skF_5', B_850, C_851), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_850, C_851)))), inference(resolution, [status(thm)], [c_35902, c_67])).
% 28.64/16.52  tff(c_36792, plain, (![B_850, C_851]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_850, C_851)))), inference(resolution, [status(thm)], [c_36718, c_3229])).
% 28.64/16.52  tff(c_43826, plain, (![B_850, C_851]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_850, C_851)))), inference(splitLeft, [status(thm)], [c_36792])).
% 28.64/16.52  tff(c_36791, plain, (![B_850, C_851]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_850, C_851)))), inference(resolution, [status(thm)], [c_36718, c_3230])).
% 28.64/16.52  tff(c_43647, plain, (![B_850, C_851]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_850, C_851)))), inference(splitLeft, [status(thm)], [c_36791])).
% 28.64/16.52  tff(c_33168, plain, (![B_814, C_815]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(resolution, [status(thm)], [c_33111, c_3297])).
% 28.64/16.52  tff(c_43469, plain, (![B_814, C_815]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(splitLeft, [status(thm)], [c_33168])).
% 28.64/16.52  tff(c_33180, plain, (![B_814, C_815]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(resolution, [status(thm)], [c_33111, c_3749])).
% 28.64/16.52  tff(c_43292, plain, (![B_814, C_815]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_814, C_815)))), inference(splitLeft, [status(thm)], [c_33180])).
% 28.64/16.52  tff(c_13968, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_13772, c_67])).
% 28.64/16.52  tff(c_31169, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_13968, c_31034])).
% 28.64/16.52  tff(c_43116, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_31169])).
% 28.64/16.52  tff(c_32677, plain, (![B_807, C_808]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(resolution, [status(thm)], [c_32608, c_3749])).
% 28.64/16.52  tff(c_42820, plain, (![B_807, C_808]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(splitLeft, [status(thm)], [c_32677])).
% 28.64/16.52  tff(c_13697, plain, (![B_38, C_39]: (r2_hidden('#skF_3'('#skF_5', B_38, C_39), k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_13677, c_67])).
% 28.64/16.52  tff(c_31170, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_13697, c_31034])).
% 28.64/16.52  tff(c_42517, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_31170])).
% 28.64/16.52  tff(c_36546, plain, (![B_848, C_849]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(resolution, [status(thm)], [c_36472, c_3229])).
% 28.64/16.52  tff(c_42344, plain, (![B_848, C_849]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(splitLeft, [status(thm)], [c_36546])).
% 28.64/16.52  tff(c_32665, plain, (![B_807, C_808]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(resolution, [status(thm)], [c_32608, c_3297])).
% 28.64/16.52  tff(c_41235, plain, (![B_807, C_808]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_807, C_808)))), inference(splitLeft, [status(thm)], [c_32665])).
% 28.64/16.52  tff(c_36545, plain, (![B_848, C_849]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(resolution, [status(thm)], [c_36472, c_3230])).
% 28.64/16.52  tff(c_40869, plain, (![B_848, C_849]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(splitLeft, [status(thm)], [c_36545])).
% 28.64/16.52  tff(c_31196, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3948, c_31034])).
% 28.64/16.52  tff(c_39771, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_31196])).
% 28.64/16.52  tff(c_31197, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_4117, c_31034])).
% 28.64/16.52  tff(c_39407, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_31197])).
% 28.64/16.52  tff(c_31195, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_4199, c_31034])).
% 28.64/16.52  tff(c_39242, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_31195])).
% 28.64/16.52  tff(c_31199, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3472, c_31034])).
% 28.64/16.52  tff(c_38457, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_31199])).
% 28.64/16.52  tff(c_38155, plain, (![B_863, C_864]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_863, C_864)))), inference(resolution, [status(thm)], [c_38076, c_1336])).
% 28.64/16.52  tff(c_38166, plain, (![B_863, C_864]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_863, C_864)))), inference(splitLeft, [status(thm)], [c_38155])).
% 28.64/16.52  tff(c_37289, plain, (![B_854, C_855]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_854, C_855)))), inference(resolution, [status(thm)], [c_37213, c_1336])).
% 28.64/16.52  tff(c_37300, plain, (![B_854, C_855]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_854, C_855)))), inference(splitLeft, [status(thm)], [c_37289])).
% 28.64/16.52  tff(c_37041, plain, (![B_852, C_853]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_852, C_853)))), inference(resolution, [status(thm)], [c_36965, c_1336])).
% 28.64/16.52  tff(c_37052, plain, (![B_852, C_853]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_852, C_853)))), inference(splitLeft, [status(thm)], [c_37041])).
% 28.64/16.52  tff(c_36794, plain, (![B_850, C_851]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_850, C_851)))), inference(resolution, [status(thm)], [c_36718, c_1336])).
% 28.64/16.52  tff(c_36805, plain, (![B_850, C_851]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_850, C_851)))), inference(splitLeft, [status(thm)], [c_36794])).
% 28.64/16.52  tff(c_36548, plain, (![B_848, C_849]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(resolution, [status(thm)], [c_36472, c_1336])).
% 28.64/16.52  tff(c_36559, plain, (![B_848, C_849]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_848, C_849)))), inference(splitLeft, [status(thm)], [c_36548])).
% 28.64/16.52  tff(c_36686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36559, c_36330])).
% 28.64/16.52  tff(c_36687, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_36548])).
% 28.64/16.52  tff(c_36933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36805, c_36687])).
% 28.64/16.52  tff(c_36934, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_36794])).
% 28.64/16.52  tff(c_37181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37052, c_36934])).
% 28.64/16.52  tff(c_37182, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_37041])).
% 28.64/16.52  tff(c_37430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37300, c_37182])).
% 28.64/16.52  tff(c_37431, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_37289])).
% 28.64/16.52  tff(c_38297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38166, c_37431])).
% 28.64/16.52  tff(c_38298, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_38155])).
% 28.64/16.52  tff(c_38589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38457, c_38298])).
% 28.64/16.52  tff(c_38590, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31199])).
% 28.64/16.52  tff(c_39375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39242, c_38590])).
% 28.64/16.52  tff(c_39376, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31195])).
% 28.64/16.52  tff(c_39739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39407, c_39376])).
% 28.64/16.52  tff(c_39740, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31197])).
% 28.64/16.52  tff(c_40837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39771, c_39740])).
% 28.64/16.52  tff(c_40838, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31196])).
% 28.64/16.52  tff(c_41005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40869, c_40838])).
% 28.64/16.52  tff(c_41006, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_36545])).
% 28.64/16.52  tff(c_41372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41235, c_41006])).
% 28.64/16.52  tff(c_41373, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_32665])).
% 28.64/16.52  tff(c_42482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42344, c_41373])).
% 28.64/16.52  tff(c_42483, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_36546])).
% 28.64/16.52  tff(c_42656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42517, c_42483])).
% 28.64/16.52  tff(c_42657, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31170])).
% 28.64/16.52  tff(c_42960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42820, c_42657])).
% 28.64/16.52  tff(c_42961, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_32677])).
% 28.64/16.52  tff(c_43257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43116, c_42961])).
% 28.64/16.52  tff(c_43258, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_31169])).
% 28.64/16.52  tff(c_43434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43292, c_43258])).
% 28.64/16.52  tff(c_43435, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_33180])).
% 28.64/16.52  tff(c_43612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43469, c_43435])).
% 28.64/16.52  tff(c_43613, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_33168])).
% 28.64/16.52  tff(c_43791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43647, c_43613])).
% 28.64/16.52  tff(c_43792, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_36791])).
% 28.64/16.52  tff(c_43971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43826, c_43792])).
% 28.64/16.52  tff(c_43972, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_36792])).
% 28.64/16.52  tff(c_44152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44006, c_43972])).
% 28.64/16.52  tff(c_44153, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_38152])).
% 28.64/16.52  tff(c_44334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44187, c_44153])).
% 28.64/16.52  tff(c_44335, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_37287])).
% 28.64/16.52  tff(c_44715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44567, c_44335])).
% 28.64/16.52  tff(c_44716, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_37038])).
% 28.64/16.52  tff(c_45524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45375, c_44716])).
% 28.64/16.52  tff(c_45525, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_37039])).
% 28.64/16.52  tff(c_54654, plain, (![B_1054, C_1055]: (r2_hidden('#skF_3'('#skF_5', B_1054, C_1055), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(resolution, [status(thm)], [c_45525, c_67])).
% 28.64/16.52  tff(c_54745, plain, (![B_1054, C_1055]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(resolution, [status(thm)], [c_54654, c_1336])).
% 28.64/16.52  tff(c_54756, plain, (![B_1054, C_1055]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(splitLeft, [status(thm)], [c_54745])).
% 28.64/16.52  tff(c_37286, plain, (![B_854, C_855]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_854, C_855)))), inference(resolution, [status(thm)], [c_37213, c_3230])).
% 28.64/16.52  tff(c_45873, plain, (![B_854, C_855]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_854, C_855)))), inference(splitLeft, [status(thm)], [c_37286])).
% 28.64/16.52  tff(c_38153, plain, (![B_863, C_864]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_863, C_864)))), inference(resolution, [status(thm)], [c_38076, c_3229])).
% 28.64/16.52  tff(c_45559, plain, (![B_863, C_864]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_863, C_864)))), inference(splitLeft, [status(thm)], [c_38153])).
% 28.64/16.52  tff(c_45838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45559, c_45525])).
% 28.64/16.52  tff(c_45839, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_38153])).
% 28.64/16.52  tff(c_46649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45873, c_45839])).
% 28.64/16.52  tff(c_46650, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_37286])).
% 28.64/16.52  tff(c_54088, plain, (![B_1046, C_1047]: (r2_hidden('#skF_3'('#skF_5', B_1046, C_1047), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1046, C_1047)))), inference(resolution, [status(thm)], [c_46650, c_67])).
% 28.64/16.52  tff(c_54179, plain, (![B_1046, C_1047]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1046, C_1047)))), inference(resolution, [status(thm)], [c_54088, c_1336])).
% 28.64/16.52  tff(c_54190, plain, (![B_1046, C_1047]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1046, C_1047)))), inference(splitLeft, [status(thm)], [c_54179])).
% 28.64/16.52  tff(c_53770, plain, (![B_1040, C_1041]: (r2_hidden('#skF_3'('#skF_5', B_1040, C_1041), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1040, C_1041)))), inference(resolution, [status(thm)], [c_45839, c_67])).
% 28.64/16.52  tff(c_53861, plain, (![B_1040, C_1041]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1040, C_1041)))), inference(resolution, [status(thm)], [c_53770, c_1336])).
% 28.64/16.52  tff(c_53872, plain, (![B_1040, C_1041]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1040, C_1041)))), inference(splitLeft, [status(thm)], [c_53861])).
% 28.64/16.52  tff(c_53218, plain, (![B_1032, C_1033]: (r2_hidden('#skF_3'('#skF_5', B_1032, C_1033), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1032, C_1033)))), inference(resolution, [status(thm)], [c_44153, c_67])).
% 28.64/16.52  tff(c_53309, plain, (![B_1032, C_1033]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1032, C_1033)))), inference(resolution, [status(thm)], [c_53218, c_1336])).
% 28.64/16.52  tff(c_53320, plain, (![B_1032, C_1033]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1032, C_1033)))), inference(splitLeft, [status(thm)], [c_53309])).
% 28.64/16.52  tff(c_52902, plain, (![B_1026, C_1027]: (r2_hidden('#skF_3'('#skF_5', B_1026, C_1027), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1026, C_1027)))), inference(resolution, [status(thm)], [c_43792, c_67])).
% 28.64/16.52  tff(c_52993, plain, (![B_1026, C_1027]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1026, C_1027)))), inference(resolution, [status(thm)], [c_52902, c_1336])).
% 28.64/16.52  tff(c_53004, plain, (![B_1026, C_1027]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1026, C_1027)))), inference(splitLeft, [status(thm)], [c_52993])).
% 28.64/16.52  tff(c_52352, plain, (![B_1018, C_1019]: (r2_hidden('#skF_3'('#skF_5', B_1018, C_1019), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1018, C_1019)))), inference(resolution, [status(thm)], [c_43972, c_67])).
% 28.64/16.52  tff(c_52443, plain, (![B_1018, C_1019]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1018, C_1019)))), inference(resolution, [status(thm)], [c_52352, c_1336])).
% 28.64/16.52  tff(c_52454, plain, (![B_1018, C_1019]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1018, C_1019)))), inference(splitLeft, [status(thm)], [c_52443])).
% 28.64/16.52  tff(c_52038, plain, (![B_1012, C_1013]: (r2_hidden('#skF_3'('#skF_5', B_1012, C_1013), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1012, C_1013)))), inference(resolution, [status(thm)], [c_44335, c_67])).
% 28.64/16.52  tff(c_52129, plain, (![B_1012, C_1013]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1012, C_1013)))), inference(resolution, [status(thm)], [c_52038, c_1336])).
% 28.64/16.52  tff(c_52140, plain, (![B_1012, C_1013]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1012, C_1013)))), inference(splitLeft, [status(thm)], [c_52129])).
% 28.64/16.52  tff(c_51616, plain, (![B_1005, C_1006]: (r2_hidden('#skF_3'('#skF_5', B_1005, C_1006), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1005, C_1006)))), inference(resolution, [status(thm)], [c_44716, c_67])).
% 28.64/16.52  tff(c_51707, plain, (![B_1005, C_1006]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1005, C_1006)))), inference(resolution, [status(thm)], [c_51616, c_1336])).
% 28.64/16.52  tff(c_51718, plain, (![B_1005, C_1006]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1005, C_1006)))), inference(splitLeft, [status(thm)], [c_51707])).
% 28.64/16.52  tff(c_51304, plain, (![B_999, C_1000]: (r2_hidden('#skF_3'('#skF_5', B_999, C_1000), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_999, C_1000)))), inference(resolution, [status(thm)], [c_43258, c_67])).
% 28.64/16.52  tff(c_51395, plain, (![B_999, C_1000]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_999, C_1000)))), inference(resolution, [status(thm)], [c_51304, c_1336])).
% 28.64/16.52  tff(c_51406, plain, (![B_999, C_1000]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_999, C_1000)))), inference(splitLeft, [status(thm)], [c_51395])).
% 28.64/16.52  tff(c_50884, plain, (![B_992, C_993]: (r2_hidden('#skF_3'('#skF_5', B_992, C_993), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_992, C_993)))), inference(resolution, [status(thm)], [c_42961, c_67])).
% 28.64/16.52  tff(c_50975, plain, (![B_992, C_993]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_992, C_993)))), inference(resolution, [status(thm)], [c_50884, c_1336])).
% 28.64/16.52  tff(c_50986, plain, (![B_992, C_993]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_992, C_993)))), inference(splitLeft, [status(thm)], [c_50975])).
% 28.64/16.52  tff(c_50574, plain, (![B_986, C_987]: (r2_hidden('#skF_3'('#skF_5', B_986, C_987), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_986, C_987)))), inference(resolution, [status(thm)], [c_41373, c_67])).
% 28.64/16.52  tff(c_50665, plain, (![B_986, C_987]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_986, C_987)))), inference(resolution, [status(thm)], [c_50574, c_1336])).
% 28.64/16.52  tff(c_50676, plain, (![B_986, C_987]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_986, C_987)))), inference(splitLeft, [status(thm)], [c_50665])).
% 28.64/16.52  tff(c_50156, plain, (![B_979, C_980]: (r2_hidden('#skF_3'('#skF_5', B_979, C_980), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_979, C_980)))), inference(resolution, [status(thm)], [c_43435, c_67])).
% 28.64/16.52  tff(c_50247, plain, (![B_979, C_980]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_979, C_980)))), inference(resolution, [status(thm)], [c_50156, c_1336])).
% 28.64/16.52  tff(c_50258, plain, (![B_979, C_980]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_979, C_980)))), inference(splitLeft, [status(thm)], [c_50247])).
% 28.64/16.52  tff(c_49848, plain, (![B_973, C_974]: (r2_hidden('#skF_3'('#skF_5', B_973, C_974), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_973, C_974)))), inference(resolution, [status(thm)], [c_42483, c_67])).
% 28.64/16.52  tff(c_49939, plain, (![B_973, C_974]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_973, C_974)))), inference(resolution, [status(thm)], [c_49848, c_1336])).
% 28.64/16.52  tff(c_49950, plain, (![B_973, C_974]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_973, C_974)))), inference(splitLeft, [status(thm)], [c_49939])).
% 28.64/16.52  tff(c_49432, plain, (![B_966, C_967]: (r2_hidden('#skF_3'('#skF_5', B_966, C_967), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_966, C_967)))), inference(resolution, [status(thm)], [c_41006, c_67])).
% 28.64/16.52  tff(c_49523, plain, (![B_966, C_967]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_966, C_967)))), inference(resolution, [status(thm)], [c_49432, c_1336])).
% 28.64/16.52  tff(c_49534, plain, (![B_966, C_967]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_966, C_967)))), inference(splitLeft, [status(thm)], [c_49523])).
% 28.64/16.52  tff(c_49126, plain, (![B_960, C_961]: (r2_hidden('#skF_3'('#skF_5', B_960, C_961), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_960, C_961)))), inference(resolution, [status(thm)], [c_42657, c_67])).
% 28.64/16.52  tff(c_49217, plain, (![B_960, C_961]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_960, C_961)))), inference(resolution, [status(thm)], [c_49126, c_1336])).
% 28.64/16.52  tff(c_49228, plain, (![B_960, C_961]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_960, C_961)))), inference(splitLeft, [status(thm)], [c_49217])).
% 28.64/16.52  tff(c_48833, plain, (![B_958, C_959]: (r2_hidden('#skF_3'('#skF_5', B_958, C_959), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_958, C_959)))), inference(resolution, [status(thm)], [c_43613, c_67])).
% 28.64/16.52  tff(c_48924, plain, (![B_958, C_959]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_958, C_959)))), inference(resolution, [status(thm)], [c_48833, c_1336])).
% 28.64/16.52  tff(c_48935, plain, (![B_958, C_959]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_958, C_959)))), inference(splitLeft, [status(thm)], [c_48924])).
% 28.64/16.52  tff(c_48529, plain, (![B_952, C_953]: (r2_hidden('#skF_3'('#skF_5', B_952, C_953), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_952, C_953)))), inference(resolution, [status(thm)], [c_38590, c_67])).
% 28.64/16.52  tff(c_48620, plain, (![B_952, C_953]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_952, C_953)))), inference(resolution, [status(thm)], [c_48529, c_1336])).
% 28.64/16.52  tff(c_48631, plain, (![B_952, C_953]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_952, C_953)))), inference(splitLeft, [status(thm)], [c_48620])).
% 28.64/16.52  tff(c_48017, plain, (![B_944, C_945]: (r2_hidden('#skF_3'('#skF_5', B_944, C_945), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_944, C_945)))), inference(resolution, [status(thm)], [c_39740, c_67])).
% 28.64/16.52  tff(c_48105, plain, (![B_944, C_945]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_944, C_945)))), inference(resolution, [status(thm)], [c_48017, c_1336])).
% 28.64/16.52  tff(c_48116, plain, (![B_944, C_945]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_944, C_945)))), inference(splitLeft, [status(thm)], [c_48105])).
% 28.64/16.52  tff(c_47099, plain, (![B_935, C_936]: (r2_hidden('#skF_3'('#skF_5', B_935, C_936), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_935, C_936)))), inference(resolution, [status(thm)], [c_39376, c_67])).
% 28.64/16.52  tff(c_47187, plain, (![B_935, C_936]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_935, C_936)))), inference(resolution, [status(thm)], [c_47099, c_1336])).
% 28.64/16.52  tff(c_47198, plain, (![B_935, C_936]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_935, C_936)))), inference(splitLeft, [status(thm)], [c_47187])).
% 28.64/16.52  tff(c_46684, plain, (![B_929, C_930]: (r2_hidden('#skF_3'('#skF_5', B_929, C_930), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_929, C_930)))), inference(resolution, [status(thm)], [c_40838, c_67])).
% 28.64/16.52  tff(c_46772, plain, (![B_929, C_930]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_929, C_930)))), inference(resolution, [status(thm)], [c_46684, c_1336])).
% 28.64/16.52  tff(c_46783, plain, (![B_929, C_930]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_929, C_930)))), inference(splitLeft, [status(thm)], [c_46772])).
% 28.64/16.52  tff(c_46935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46783, c_46650])).
% 28.64/16.52  tff(c_46936, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_46772])).
% 28.64/16.52  tff(c_47982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47198, c_46936])).
% 28.64/16.52  tff(c_47983, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_47187])).
% 28.64/16.52  tff(c_48270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48116, c_47983])).
% 28.64/16.52  tff(c_48271, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_48105])).
% 28.64/16.52  tff(c_48798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48631, c_48271])).
% 28.64/16.52  tff(c_48799, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_48620])).
% 28.64/16.52  tff(c_49091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48935, c_48799])).
% 28.64/16.52  tff(c_49092, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_48924])).
% 28.64/16.52  tff(c_49397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49228, c_49092])).
% 28.64/16.52  tff(c_49398, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_49217])).
% 28.64/16.52  tff(c_49692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49534, c_49398])).
% 28.64/16.52  tff(c_49693, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_49523])).
% 28.64/16.52  tff(c_50121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49950, c_49693])).
% 28.64/16.52  tff(c_50122, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_49939])).
% 28.64/16.52  tff(c_50418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50258, c_50122])).
% 28.64/16.52  tff(c_50419, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_50247])).
% 28.64/16.52  tff(c_50849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50676, c_50419])).
% 28.64/16.52  tff(c_50850, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_50665])).
% 28.64/16.52  tff(c_51148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50986, c_50850])).
% 28.64/16.52  tff(c_51149, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_50975])).
% 28.64/16.52  tff(c_51581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51406, c_51149])).
% 28.64/16.52  tff(c_51582, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_51395])).
% 28.64/16.52  tff(c_51882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51718, c_51582])).
% 28.64/16.52  tff(c_51883, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_51707])).
% 28.64/16.52  tff(c_52317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52140, c_51883])).
% 28.64/16.52  tff(c_52318, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_52129])).
% 28.64/16.52  tff(c_52620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52454, c_52318])).
% 28.64/16.52  tff(c_52621, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_52443])).
% 28.64/16.52  tff(c_53183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53004, c_52621])).
% 28.64/16.52  tff(c_53184, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_52993])).
% 28.64/16.52  tff(c_53488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53320, c_53184])).
% 28.64/16.52  tff(c_53489, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_53309])).
% 28.64/16.52  tff(c_54053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53872, c_53489])).
% 28.64/16.52  tff(c_54054, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_53861])).
% 28.64/16.52  tff(c_54360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54190, c_54054])).
% 28.64/16.52  tff(c_54361, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_54179])).
% 28.64/16.52  tff(c_54939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54756, c_54361])).
% 28.64/16.52  tff(c_54940, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_54745])).
% 28.64/16.52  tff(c_55146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54974, c_54940])).
% 28.64/16.52  tff(c_55147, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_36532])).
% 28.64/16.52  tff(c_55601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55428, c_55147])).
% 28.64/16.52  tff(c_55602, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_36544])).
% 28.64/16.52  tff(c_55835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55659, c_55602])).
% 28.64/16.52  tff(c_55836, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_9', '#skF_7')))), inference(splitRight, [status(thm)], [c_55657])).
% 28.64/16.52  tff(c_64, plain, (![C_39, B_38, D_15, A_37, C_14]: (r2_hidden('#skF_4'(A_37, B_38, C_39), D_15) | ~r2_hidden(A_37, k2_zfmisc_1(C_14, D_15)) | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_24])).
% 28.64/16.52  tff(c_55870, plain, (![B_1073, C_1074]: (r2_hidden('#skF_4'('#skF_5', B_1073, C_1074), k3_xboole_0('#skF_9', '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1073, C_1074)))), inference(resolution, [status(thm)], [c_55836, c_64])).
% 28.64/16.52  tff(c_55644, plain, (![A_1066, B_57, C_59]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1066, '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_5', B_57, C_59), A_1066) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_199, c_55636])).
% 28.64/16.52  tff(c_55927, plain, (![B_1073, C_1074]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1073, C_1074)))), inference(resolution, [status(thm)], [c_55870, c_55644])).
% 28.64/16.52  tff(c_56201, plain, (![B_1073, C_1074]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1073, C_1074)))), inference(splitLeft, [status(thm)], [c_55927])).
% 28.64/16.52  tff(c_56378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56201, c_55836])).
% 28.64/16.52  tff(c_56379, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_55927])).
% 28.64/16.52  tff(c_56607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56428, c_56379])).
% 28.64/16.52  tff(c_56608, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_56424])).
% 28.64/16.52  tff(c_56642, plain, (![B_1084, C_1085]: (r2_hidden('#skF_4'('#skF_5', B_1084, C_1085), k3_xboole_0('#skF_7', '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1084, C_1085)))), inference(resolution, [status(thm)], [c_56608, c_64])).
% 28.64/16.52  tff(c_61, plain, (![C_39, B_38, D_15, A_37, C_14]: (r2_hidden(A_37, k2_zfmisc_1(C_14, D_15)) | ~r2_hidden('#skF_4'(A_37, B_38, C_39), D_15) | ~r2_hidden('#skF_3'(A_37, B_38, C_39), C_14) | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_22])).
% 28.64/16.52  tff(c_68338, plain, (![C_1238, B_1239, C_1240]: (r2_hidden('#skF_5', k2_zfmisc_1(C_1238, k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_3'('#skF_5', B_1239, C_1240), C_1238) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1239, C_1240)))), inference(resolution, [status(thm)], [c_56642, c_61])).
% 28.64/16.52  tff(c_68494, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_3714, c_68338])).
% 28.64/16.52  tff(c_68585, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(negUnitSimplification, [status(thm)], [c_28, c_68494])).
% 28.64/16.52  tff(c_55869, plain, (![B_38, C_39]: (r2_hidden('#skF_4'('#skF_5', B_38, C_39), k3_xboole_0('#skF_9', '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_55836, c_64])).
% 28.64/16.52  tff(c_56423, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_55869, c_56413])).
% 28.64/16.52  tff(c_56729, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_56423])).
% 28.64/16.52  tff(c_57164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56729, c_56608])).
% 28.64/16.52  tff(c_57165, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56423])).
% 28.64/16.52  tff(c_57198, plain, (![B_38, C_39]: (r2_hidden('#skF_4'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57165, c_64])).
% 28.64/16.52  tff(c_58166, plain, (![A_1108, B_1109, B_1110, C_1111]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1108, B_1109))) | ~r2_hidden('#skF_4'('#skF_5', B_1110, C_1111), B_1109) | ~r2_hidden('#skF_4'('#skF_5', B_1110, C_1111), A_1108) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1110, C_1111)))), inference(resolution, [status(thm)], [c_252, c_48272])).
% 28.64/16.52  tff(c_60866, plain, (![A_1138, B_1139, C_1140]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1138, '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_5', B_1139, C_1140), A_1138) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1139, C_1140)))), inference(resolution, [status(thm)], [c_199, c_58166])).
% 28.64/16.52  tff(c_60886, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57198, c_60866])).
% 28.64/16.52  tff(c_64784, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_60886])).
% 28.64/16.52  tff(c_55645, plain, (![A_1066, B_57, C_59]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1066, '#skF_9'))) | ~r2_hidden('#skF_4'('#skF_5', B_57, C_59), A_1066) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_198, c_55636])).
% 28.64/16.52  tff(c_56701, plain, (![B_1084, C_1085]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1084, C_1085)))), inference(resolution, [status(thm)], [c_56642, c_55645])).
% 28.64/16.52  tff(c_57199, plain, (![B_1084, C_1085]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1084, C_1085)))), inference(splitLeft, [status(thm)], [c_56701])).
% 28.64/16.52  tff(c_57398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57199, c_57165])).
% 28.64/16.52  tff(c_57399, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56701])).
% 28.64/16.52  tff(c_57432, plain, (![B_38, C_39]: (r2_hidden('#skF_4'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57399, c_64])).
% 28.64/16.52  tff(c_60887, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57432, c_60866])).
% 28.64/16.52  tff(c_64118, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_60887])).
% 28.64/16.52  tff(c_56702, plain, (![B_1084, C_1085]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1084, C_1085)))), inference(resolution, [status(thm)], [c_56642, c_55644])).
% 28.64/16.52  tff(c_57433, plain, (![B_1084, C_1085]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1084, C_1085)))), inference(splitLeft, [status(thm)], [c_56702])).
% 28.64/16.52  tff(c_57615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57433, c_57399])).
% 28.64/16.52  tff(c_57616, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_56702])).
% 28.64/16.52  tff(c_57649, plain, (![B_38, C_39]: (r2_hidden('#skF_4'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57616, c_64])).
% 28.64/16.52  tff(c_59936, plain, (![A_1129, B_1130, C_1131]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1129, '#skF_9'))) | ~r2_hidden('#skF_4'('#skF_5', B_1130, C_1131), A_1129) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1130, C_1131)))), inference(resolution, [status(thm)], [c_198, c_58166])).
% 28.64/16.52  tff(c_59958, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57649, c_59936])).
% 28.64/16.52  tff(c_63815, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_59958])).
% 28.64/16.52  tff(c_56412, plain, (![B_38, C_39]: (r2_hidden('#skF_4'('#skF_5', B_38, C_39), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_56379, c_64])).
% 28.64/16.52  tff(c_60889, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_56412, c_60866])).
% 28.64/16.52  tff(c_63575, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_60889])).
% 28.64/16.52  tff(c_59956, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57198, c_59936])).
% 28.64/16.52  tff(c_63274, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_59956])).
% 28.64/16.52  tff(c_60888, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57649, c_60866])).
% 28.64/16.52  tff(c_63037, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_60888])).
% 28.64/16.52  tff(c_58192, plain, (![B_1112, C_1113]: (r2_hidden('#skF_4'('#skF_5', B_1112, C_1113), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1112, C_1113)))), inference(resolution, [status(thm)], [c_57165, c_64])).
% 28.64/16.52  tff(c_58254, plain, (![B_1112, C_1113]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1112, C_1113)))), inference(resolution, [status(thm)], [c_58192, c_55645])).
% 28.64/16.52  tff(c_62792, plain, (![B_1112, C_1113]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1112, C_1113)))), inference(splitLeft, [status(thm)], [c_58254])).
% 28.64/16.52  tff(c_58255, plain, (![B_1112, C_1113]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1112, C_1113)))), inference(resolution, [status(thm)], [c_58192, c_55644])).
% 28.64/16.52  tff(c_62494, plain, (![B_1112, C_1113]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1112, C_1113)))), inference(splitLeft, [status(thm)], [c_58255])).
% 28.64/16.52  tff(c_59957, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_57432, c_59936])).
% 28.64/16.52  tff(c_62260, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_59957])).
% 28.64/16.52  tff(c_57905, plain, (![B_1102, C_1103]: (r2_hidden('#skF_4'('#skF_5', B_1102, C_1103), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1102, C_1103)))), inference(resolution, [status(thm)], [c_56379, c_64])).
% 28.64/16.52  tff(c_57965, plain, (![B_1102, C_1103]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1102, C_1103)))), inference(resolution, [status(thm)], [c_57905, c_55644])).
% 28.64/16.52  tff(c_62002, plain, (![B_1102, C_1103]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1102, C_1103)))), inference(splitLeft, [status(thm)], [c_57965])).
% 28.64/16.52  tff(c_59959, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_56412, c_59936])).
% 28.64/16.52  tff(c_61707, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_59959])).
% 28.64/16.52  tff(c_60891, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_55869, c_60866])).
% 28.64/16.52  tff(c_61451, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_60891])).
% 28.64/16.52  tff(c_56641, plain, (![B_38, C_39]: (r2_hidden('#skF_4'('#skF_5', B_38, C_39), k3_xboole_0('#skF_7', '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_56608, c_64])).
% 28.64/16.52  tff(c_60890, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_56641, c_60866])).
% 28.64/16.52  tff(c_61158, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_60890])).
% 28.64/16.52  tff(c_60894, plain, (![B_57, C_59]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_9', '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_198, c_60866])).
% 28.64/16.52  tff(c_60929, plain, (![B_57, C_59]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(splitLeft, [status(thm)], [c_60894])).
% 28.64/16.52  tff(c_59961, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_55869, c_59936])).
% 28.64/16.52  tff(c_60672, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_59961])).
% 28.64/16.52  tff(c_59960, plain, (![B_38, C_39]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(resolution, [status(thm)], [c_56641, c_59936])).
% 28.64/16.52  tff(c_60191, plain, (![B_38, C_39]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_38, C_39)))), inference(splitLeft, [status(thm)], [c_59960])).
% 28.64/16.52  tff(c_59962, plain, (![B_57, C_59]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(resolution, [status(thm)], [c_199, c_59936])).
% 28.64/16.52  tff(c_59966, plain, (![B_57, C_59]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_57, C_59)))), inference(splitLeft, [status(thm)], [c_59962])).
% 28.64/16.52  tff(c_57992, plain, (![B_1104, C_1105]: (r2_hidden('#skF_4'('#skF_5', B_1104, C_1105), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1104, C_1105)))), inference(resolution, [status(thm)], [c_57616, c_64])).
% 28.64/16.52  tff(c_58051, plain, (![B_1104, C_1105]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1104, C_1105)))), inference(resolution, [status(thm)], [c_57992, c_55645])).
% 28.64/16.52  tff(c_59713, plain, (![B_1104, C_1105]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1104, C_1105)))), inference(splitLeft, [status(thm)], [c_58051])).
% 28.64/16.52  tff(c_58052, plain, (![B_1104, C_1105]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1104, C_1105)))), inference(resolution, [status(thm)], [c_57992, c_55644])).
% 28.64/16.52  tff(c_59232, plain, (![B_1104, C_1105]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1104, C_1105)))), inference(splitLeft, [status(thm)], [c_58052])).
% 28.64/16.52  tff(c_58079, plain, (![B_1106, C_1107]: (r2_hidden('#skF_4'('#skF_5', B_1106, C_1107), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1106, C_1107)))), inference(resolution, [status(thm)], [c_57399, c_64])).
% 28.64/16.52  tff(c_58138, plain, (![B_1106, C_1107]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1106, C_1107)))), inference(resolution, [status(thm)], [c_58079, c_55645])).
% 28.64/16.52  tff(c_58980, plain, (![B_1106, C_1107]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1106, C_1107)))), inference(splitLeft, [status(thm)], [c_58138])).
% 28.64/16.52  tff(c_58139, plain, (![B_1106, C_1107]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1106, C_1107)))), inference(resolution, [status(thm)], [c_58079, c_55644])).
% 28.64/16.52  tff(c_58501, plain, (![B_1106, C_1107]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1106, C_1107)))), inference(splitLeft, [status(thm)], [c_58139])).
% 28.64/16.52  tff(c_57964, plain, (![B_1102, C_1103]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1102, C_1103)))), inference(resolution, [status(thm)], [c_57905, c_55645])).
% 28.64/16.52  tff(c_58282, plain, (![B_1102, C_1103]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1102, C_1103)))), inference(splitLeft, [status(thm)], [c_57964])).
% 28.64/16.52  tff(c_58466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58282, c_57616])).
% 28.64/16.52  tff(c_58467, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_57964])).
% 28.64/16.52  tff(c_58945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58501, c_58467])).
% 28.64/16.52  tff(c_58946, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_58139])).
% 28.64/16.52  tff(c_59197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58980, c_58946])).
% 28.64/16.52  tff(c_59198, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_58138])).
% 28.64/16.52  tff(c_59419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59232, c_59198])).
% 28.64/16.52  tff(c_59420, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_58052])).
% 28.64/16.52  tff(c_59901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59713, c_59420])).
% 28.64/16.52  tff(c_59902, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_58051])).
% 28.64/16.52  tff(c_60156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59966, c_59902])).
% 28.64/16.52  tff(c_60157, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_59962])).
% 28.64/16.52  tff(c_60382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60191, c_60157])).
% 28.64/16.52  tff(c_60383, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_59960])).
% 28.64/16.52  tff(c_60864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60672, c_60383])).
% 28.64/16.52  tff(c_60865, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_59961])).
% 28.64/16.52  tff(c_61123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60929, c_60865])).
% 28.64/16.52  tff(c_61124, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_9', '#skF_7')))), inference(splitRight, [status(thm)], [c_60894])).
% 28.64/16.52  tff(c_61416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61158, c_61124])).
% 28.64/16.52  tff(c_61417, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_60890])).
% 28.64/16.52  tff(c_61672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61451, c_61417])).
% 28.64/16.52  tff(c_61673, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_60891])).
% 28.64/16.52  tff(c_61904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61707, c_61673])).
% 28.64/16.52  tff(c_61905, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_59959])).
% 28.64/16.52  tff(c_62200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62002, c_61905])).
% 28.64/16.52  tff(c_62201, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_57965])).
% 28.64/16.52  tff(c_62459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62260, c_62201])).
% 28.64/16.52  tff(c_62460, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_59957])).
% 28.64/16.52  tff(c_62694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62494, c_62460])).
% 28.64/16.52  tff(c_62695, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_58255])).
% 28.64/16.52  tff(c_62993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62792, c_62695])).
% 28.64/16.52  tff(c_62994, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_58254])).
% 28.64/16.52  tff(c_63239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63037, c_62994])).
% 28.64/16.52  tff(c_63240, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_60888])).
% 28.64/16.52  tff(c_63540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63274, c_63240])).
% 28.64/16.52  tff(c_63541, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_59956])).
% 28.64/16.52  tff(c_63780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63575, c_63541])).
% 28.64/16.52  tff(c_63781, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_60889])).
% 28.64/16.52  tff(c_64020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63815, c_63781])).
% 28.64/16.52  tff(c_64021, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_59958])).
% 28.64/16.52  tff(c_64324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64118, c_64021])).
% 28.64/16.52  tff(c_64325, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_60887])).
% 28.64/16.52  tff(c_65054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64784, c_64325])).
% 28.64/16.52  tff(c_65055, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_60886])).
% 28.64/16.52  tff(c_68801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68585, c_65055])).
% 28.64/16.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.64/16.52  
% 28.64/16.52  Inference rules
% 28.64/16.52  ----------------------
% 28.64/16.52  #Ref     : 0
% 28.64/16.52  #Sup     : 13375
% 28.64/16.52  #Fact    : 0
% 28.64/16.52  #Define  : 0
% 28.64/16.52  #Split   : 195
% 28.64/16.52  #Chain   : 0
% 28.64/16.52  #Close   : 0
% 28.64/16.52  
% 28.64/16.52  Ordering : KBO
% 28.64/16.52  
% 28.64/16.52  Simplification rules
% 28.64/16.52  ----------------------
% 28.64/16.52  #Subsume      : 13941
% 28.64/16.52  #Demod        : 1051
% 28.64/16.52  #Tautology    : 261
% 28.64/16.52  #SimpNegUnit  : 20651
% 28.64/16.52  #BackRed      : 19300
% 28.64/16.52  
% 28.64/16.52  #Partial instantiations: 0
% 28.64/16.52  #Strategies tried      : 1
% 28.64/16.52  
% 28.64/16.52  Timing (in seconds)
% 28.64/16.52  ----------------------
% 28.64/16.52  Preprocessing        : 0.28
% 28.64/16.52  Parsing              : 0.15
% 28.64/16.52  CNF conversion       : 0.02
% 28.64/16.52  Main loop            : 15.20
% 28.64/16.52  Inferencing          : 2.08
% 28.64/16.52  Reduction            : 5.38
% 28.64/16.52  Demodulation         : 4.44
% 28.64/16.52  BG Simplification    : 0.39
% 28.64/16.52  Subsumption          : 6.39
% 28.64/16.52  Abstraction          : 0.55
% 28.64/16.52  MUC search           : 0.00
% 28.64/16.52  Cooper               : 0.00
% 28.64/16.52  Total                : 15.79
% 28.64/16.52  Index Insertion      : 0.00
% 28.64/16.52  Index Deletion       : 0.00
% 28.64/16.52  Index Matching       : 0.00
% 28.64/16.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
