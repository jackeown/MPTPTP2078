%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:50 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 515 expanded)
%              Number of leaves         :   23 ( 192 expanded)
%              Depth                    :   20
%              Number of atoms          :  211 (1830 expanded)
%              Number of equality atoms :   21 ( 409 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k1_relat_1(A) = k1_relat_1(B)
                & ! [C] :
                    ( r2_hidden(C,k1_relat_1(A))
                   => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_32,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_3,B_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),A_3)
      | r1_tarski(A_3,B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [C_75,D_76,B_77,A_78] :
      ( r2_hidden(k4_tarski(C_75,D_76),B_77)
      | ~ r2_hidden(k4_tarski(C_75,D_76),A_78)
      | ~ r1_tarski(A_78,B_77)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_577,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden(k4_tarski('#skF_1'(A_107,B_108),'#skF_2'(A_107,B_108)),B_109)
      | ~ r1_tarski(A_107,B_109)
      | r1_tarski(A_107,B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_16,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k1_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(C_35,D_38),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_612,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden('#skF_1'(A_110,B_111),k1_relat_1(B_112))
      | ~ r1_tarski(A_110,B_112)
      | r1_tarski(A_110,B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_577,c_16])).

tff(c_628,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_1'(A_110,B_111),k1_relat_1('#skF_8'))
      | ~ r1_tarski(A_110,'#skF_7')
      | r1_tarski(A_110,B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_612])).

tff(c_40,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ! [A_63,B_64] :
      ( r2_hidden(k4_tarski('#skF_1'(A_63,B_64),'#skF_2'(A_63,B_64)),A_63)
      | r1_tarski(A_63,B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [C_41,A_39,B_40] :
      ( k1_funct_1(C_41,A_39) = B_40
      | ~ r2_hidden(k4_tarski(A_39,B_40),C_41)
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_218,plain,(
    ! [A_81,B_82] :
      ( k1_funct_1(A_81,'#skF_1'(A_81,B_82)) = '#skF_2'(A_81,B_82)
      | ~ v1_funct_1(A_81)
      | r1_tarski(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_99,c_28])).

tff(c_118,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),k1_relat_1(A_65))
      | r1_tarski(A_65,B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_99,c_16])).

tff(c_129,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'('#skF_7',B_66),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_7',B_66)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_118])).

tff(c_138,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_1'('#skF_7',B_67),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_7',B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_129])).

tff(c_34,plain,(
    ! [C_46] :
      ( k1_funct_1('#skF_7',C_46) = k1_funct_1('#skF_8',C_46)
      | ~ r2_hidden(C_46,k1_relat_1('#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    ! [C_46] :
      ( k1_funct_1('#skF_7',C_46) = k1_funct_1('#skF_8',C_46)
      | ~ r2_hidden(C_46,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_146,plain,(
    ! [B_67] :
      ( k1_funct_1('#skF_7','#skF_1'('#skF_7',B_67)) = k1_funct_1('#skF_8','#skF_1'('#skF_7',B_67))
      | r1_tarski('#skF_7',B_67) ) ),
    inference(resolution,[status(thm)],[c_138,c_45])).

tff(c_228,plain,(
    ! [B_82] :
      ( k1_funct_1('#skF_8','#skF_1'('#skF_7',B_82)) = '#skF_2'('#skF_7',B_82)
      | r1_tarski('#skF_7',B_82)
      | ~ v1_funct_1('#skF_7')
      | r1_tarski('#skF_7',B_82)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_146])).

tff(c_263,plain,(
    ! [B_85] :
      ( k1_funct_1('#skF_8','#skF_1'('#skF_7',B_85)) = '#skF_2'('#skF_7',B_85)
      | r1_tarski('#skF_7',B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_228])).

tff(c_26,plain,(
    ! [A_39,C_41] :
      ( r2_hidden(k4_tarski(A_39,k1_funct_1(C_41,A_39)),C_41)
      | ~ r2_hidden(A_39,k1_relat_1(C_41))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_269,plain,(
    ! [B_85] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_7',B_85),'#skF_2'('#skF_7',B_85)),'#skF_8')
      | ~ r2_hidden('#skF_1'('#skF_7',B_85),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r1_tarski('#skF_7',B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_26])).

tff(c_1346,plain,(
    ! [B_160] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_7',B_160),'#skF_2'('#skF_7',B_160)),'#skF_8')
      | ~ r2_hidden('#skF_1'('#skF_7',B_160),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_7',B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_269])).

tff(c_10,plain,(
    ! [A_3,B_13] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),B_13)
      | r1_tarski(A_3,B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1352,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k1_relat_1('#skF_8'))
    | r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1346,c_10])).

tff(c_1364,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k1_relat_1('#skF_8'))
    | r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1352])).

tff(c_1369,plain,(
    ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1364])).

tff(c_1378,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_tarski('#skF_7','#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_628,c_1369])).

tff(c_1396,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_1378])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1430,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1396,c_2])).

tff(c_1436,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1430])).

tff(c_62,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(k4_tarski(C_56,'#skF_6'(A_57,k1_relat_1(A_57),C_56)),A_57)
      | ~ r2_hidden(C_56,k1_relat_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_72,plain,(
    ! [C_56] :
      ( r2_hidden(k4_tarski(C_56,'#skF_6'('#skF_7',k1_relat_1('#skF_8'),C_56)),'#skF_7')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_62])).

tff(c_75,plain,(
    ! [C_56] :
      ( r2_hidden(k4_tarski(C_56,'#skF_6'('#skF_7',k1_relat_1('#skF_8'),C_56)),'#skF_7')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_177,plain,(
    ! [C_56,B_77] :
      ( r2_hidden(k4_tarski(C_56,'#skF_6'('#skF_7',k1_relat_1('#skF_8'),C_56)),B_77)
      | ~ r1_tarski('#skF_7',B_77)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_75,c_173])).

tff(c_413,plain,(
    ! [C_94,B_95] :
      ( r2_hidden(k4_tarski(C_94,'#skF_6'('#skF_7',k1_relat_1('#skF_8'),C_94)),B_95)
      | ~ r1_tarski('#skF_7',B_95)
      | ~ r2_hidden(C_94,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_177])).

tff(c_444,plain,(
    ! [C_94,B_95] :
      ( r2_hidden(C_94,k1_relat_1(B_95))
      | ~ r1_tarski('#skF_7',B_95)
      | ~ r2_hidden(C_94,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_413,c_16])).

tff(c_629,plain,(
    ! [A_110,B_111,B_95] :
      ( r2_hidden('#skF_1'(A_110,B_111),k1_relat_1(B_95))
      | ~ r1_tarski('#skF_7',B_95)
      | ~ r1_tarski(A_110,'#skF_8')
      | r1_tarski(A_110,B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_612,c_444])).

tff(c_609,plain,(
    ! [B_109,A_107,B_108] :
      ( k1_funct_1(B_109,'#skF_1'(A_107,B_108)) = '#skF_2'(A_107,B_108)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109)
      | ~ r1_tarski(A_107,B_109)
      | r1_tarski(A_107,B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_577,c_28])).

tff(c_126,plain,(
    ! [B_66] :
      ( k1_funct_1('#skF_7','#skF_1'('#skF_8',B_66)) = k1_funct_1('#skF_8','#skF_1'('#skF_8',B_66))
      | r1_tarski('#skF_8',B_66)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_118,c_45])).

tff(c_135,plain,(
    ! [B_66] :
      ( k1_funct_1('#skF_7','#skF_1'('#skF_8',B_66)) = k1_funct_1('#skF_8','#skF_1'('#skF_8',B_66))
      | r1_tarski('#skF_8',B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_126])).

tff(c_185,plain,(
    ! [A_79,C_80] :
      ( r2_hidden(k4_tarski(A_79,k1_funct_1(C_80,A_79)),C_80)
      | ~ r2_hidden(A_79,k1_relat_1(C_80))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_207,plain,(
    ! [B_66] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8',B_66),k1_funct_1('#skF_8','#skF_1'('#skF_8',B_66))),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8',B_66),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | r1_tarski('#skF_8',B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_185])).

tff(c_2458,plain,(
    ! [B_194] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8',B_194),k1_funct_1('#skF_8','#skF_1'('#skF_8',B_194))),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8',B_194),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_8',B_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_207])).

tff(c_2474,plain,(
    ! [B_108] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8',B_108),'#skF_2'('#skF_8',B_108)),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8',B_108),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_8',B_108)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8','#skF_8')
      | r1_tarski('#skF_8',B_108)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_2458])).

tff(c_2493,plain,(
    ! [B_195] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8',B_195),'#skF_2'('#skF_8',B_195)),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8',B_195),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_8',B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_40,c_38,c_2474])).

tff(c_2499,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_2493,c_10])).

tff(c_2511,plain,
    ( ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2499])).

tff(c_2512,plain,(
    ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1436,c_2511])).

tff(c_2520,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_629,c_2512])).

tff(c_2541,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_1396,c_2520])).

tff(c_2543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1436,c_2541])).

tff(c_2544,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1364])).

tff(c_2549,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_2544,c_2])).

tff(c_2555,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2549])).

tff(c_5012,plain,(
    ! [B_254] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8',B_254),k1_funct_1('#skF_8','#skF_1'('#skF_8',B_254))),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8',B_254),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_8',B_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_207])).

tff(c_5028,plain,(
    ! [B_108] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8',B_108),'#skF_2'('#skF_8',B_108)),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8',B_108),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_8',B_108)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8','#skF_8')
      | r1_tarski('#skF_8',B_108)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_5012])).

tff(c_5047,plain,(
    ! [B_255] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8',B_255),'#skF_2'('#skF_8',B_255)),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_8',B_255),k1_relat_1('#skF_8'))
      | r1_tarski('#skF_8',B_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_40,c_38,c_5028])).

tff(c_5053,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_5047,c_10])).

tff(c_5065,plain,
    ( ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5053])).

tff(c_5066,plain,(
    ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_2555,c_5065])).

tff(c_5074,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_629,c_5066])).

tff(c_5095,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_2544,c_5074])).

tff(c_5097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2555,c_5095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:52:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.12  
% 5.94/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.12  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.94/2.12  
% 5.94/2.12  %Foreground sorts:
% 5.94/2.12  
% 5.94/2.12  
% 5.94/2.12  %Background operators:
% 5.94/2.12  
% 5.94/2.12  
% 5.94/2.12  %Foreground operators:
% 5.94/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.94/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.94/2.12  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.94/2.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.94/2.12  tff('#skF_7', type, '#skF_7': $i).
% 5.94/2.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.94/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.94/2.12  tff('#skF_8', type, '#skF_8': $i).
% 5.94/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.94/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.94/2.12  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.94/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.94/2.12  
% 5.94/2.14  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.94/2.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.94/2.14  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 5.94/2.14  tff(f_49, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.94/2.14  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 5.94/2.14  tff(c_32, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.14  tff(c_44, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.94/2.14  tff(c_36, plain, (k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.14  tff(c_12, plain, (![A_3, B_13]: (r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), A_3) | r1_tarski(A_3, B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.94/2.14  tff(c_173, plain, (![C_75, D_76, B_77, A_78]: (r2_hidden(k4_tarski(C_75, D_76), B_77) | ~r2_hidden(k4_tarski(C_75, D_76), A_78) | ~r1_tarski(A_78, B_77) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.94/2.14  tff(c_577, plain, (![A_107, B_108, B_109]: (r2_hidden(k4_tarski('#skF_1'(A_107, B_108), '#skF_2'(A_107, B_108)), B_109) | ~r1_tarski(A_107, B_109) | r1_tarski(A_107, B_108) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_12, c_173])).
% 5.94/2.14  tff(c_16, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k1_relat_1(A_20)) | ~r2_hidden(k4_tarski(C_35, D_38), A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.94/2.14  tff(c_612, plain, (![A_110, B_111, B_112]: (r2_hidden('#skF_1'(A_110, B_111), k1_relat_1(B_112)) | ~r1_tarski(A_110, B_112) | r1_tarski(A_110, B_111) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_577, c_16])).
% 5.94/2.14  tff(c_628, plain, (![A_110, B_111]: (r2_hidden('#skF_1'(A_110, B_111), k1_relat_1('#skF_8')) | ~r1_tarski(A_110, '#skF_7') | r1_tarski(A_110, B_111) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_36, c_612])).
% 5.94/2.14  tff(c_40, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.14  tff(c_38, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.14  tff(c_42, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.14  tff(c_99, plain, (![A_63, B_64]: (r2_hidden(k4_tarski('#skF_1'(A_63, B_64), '#skF_2'(A_63, B_64)), A_63) | r1_tarski(A_63, B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.94/2.14  tff(c_28, plain, (![C_41, A_39, B_40]: (k1_funct_1(C_41, A_39)=B_40 | ~r2_hidden(k4_tarski(A_39, B_40), C_41) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.94/2.14  tff(c_218, plain, (![A_81, B_82]: (k1_funct_1(A_81, '#skF_1'(A_81, B_82))='#skF_2'(A_81, B_82) | ~v1_funct_1(A_81) | r1_tarski(A_81, B_82) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_99, c_28])).
% 5.94/2.14  tff(c_118, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), k1_relat_1(A_65)) | r1_tarski(A_65, B_66) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_99, c_16])).
% 5.94/2.14  tff(c_129, plain, (![B_66]: (r2_hidden('#skF_1'('#skF_7', B_66), k1_relat_1('#skF_8')) | r1_tarski('#skF_7', B_66) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_118])).
% 5.94/2.14  tff(c_138, plain, (![B_67]: (r2_hidden('#skF_1'('#skF_7', B_67), k1_relat_1('#skF_8')) | r1_tarski('#skF_7', B_67))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_129])).
% 5.94/2.14  tff(c_34, plain, (![C_46]: (k1_funct_1('#skF_7', C_46)=k1_funct_1('#skF_8', C_46) | ~r2_hidden(C_46, k1_relat_1('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.14  tff(c_45, plain, (![C_46]: (k1_funct_1('#skF_7', C_46)=k1_funct_1('#skF_8', C_46) | ~r2_hidden(C_46, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 5.94/2.14  tff(c_146, plain, (![B_67]: (k1_funct_1('#skF_7', '#skF_1'('#skF_7', B_67))=k1_funct_1('#skF_8', '#skF_1'('#skF_7', B_67)) | r1_tarski('#skF_7', B_67))), inference(resolution, [status(thm)], [c_138, c_45])).
% 5.94/2.14  tff(c_228, plain, (![B_82]: (k1_funct_1('#skF_8', '#skF_1'('#skF_7', B_82))='#skF_2'('#skF_7', B_82) | r1_tarski('#skF_7', B_82) | ~v1_funct_1('#skF_7') | r1_tarski('#skF_7', B_82) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_146])).
% 5.94/2.14  tff(c_263, plain, (![B_85]: (k1_funct_1('#skF_8', '#skF_1'('#skF_7', B_85))='#skF_2'('#skF_7', B_85) | r1_tarski('#skF_7', B_85))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_228])).
% 5.94/2.14  tff(c_26, plain, (![A_39, C_41]: (r2_hidden(k4_tarski(A_39, k1_funct_1(C_41, A_39)), C_41) | ~r2_hidden(A_39, k1_relat_1(C_41)) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.94/2.14  tff(c_269, plain, (![B_85]: (r2_hidden(k4_tarski('#skF_1'('#skF_7', B_85), '#skF_2'('#skF_7', B_85)), '#skF_8') | ~r2_hidden('#skF_1'('#skF_7', B_85), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r1_tarski('#skF_7', B_85))), inference(superposition, [status(thm), theory('equality')], [c_263, c_26])).
% 5.94/2.14  tff(c_1346, plain, (![B_160]: (r2_hidden(k4_tarski('#skF_1'('#skF_7', B_160), '#skF_2'('#skF_7', B_160)), '#skF_8') | ~r2_hidden('#skF_1'('#skF_7', B_160), k1_relat_1('#skF_8')) | r1_tarski('#skF_7', B_160))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_269])).
% 5.94/2.14  tff(c_10, plain, (![A_3, B_13]: (~r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), B_13) | r1_tarski(A_3, B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.94/2.14  tff(c_1352, plain, (~v1_relat_1('#skF_7') | ~r2_hidden('#skF_1'('#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_1346, c_10])).
% 5.94/2.14  tff(c_1364, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1352])).
% 5.94/2.14  tff(c_1369, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1364])).
% 5.94/2.14  tff(c_1378, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_tarski('#skF_7', '#skF_8') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_628, c_1369])).
% 5.94/2.14  tff(c_1396, plain, (r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_1378])).
% 5.94/2.14  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.94/2.14  tff(c_1430, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1396, c_2])).
% 5.94/2.14  tff(c_1436, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_1430])).
% 5.94/2.14  tff(c_62, plain, (![C_56, A_57]: (r2_hidden(k4_tarski(C_56, '#skF_6'(A_57, k1_relat_1(A_57), C_56)), A_57) | ~r2_hidden(C_56, k1_relat_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.94/2.14  tff(c_72, plain, (![C_56]: (r2_hidden(k4_tarski(C_56, '#skF_6'('#skF_7', k1_relat_1('#skF_8'), C_56)), '#skF_7') | ~r2_hidden(C_56, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_62])).
% 5.94/2.14  tff(c_75, plain, (![C_56]: (r2_hidden(k4_tarski(C_56, '#skF_6'('#skF_7', k1_relat_1('#skF_8'), C_56)), '#skF_7') | ~r2_hidden(C_56, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_72])).
% 5.94/2.14  tff(c_177, plain, (![C_56, B_77]: (r2_hidden(k4_tarski(C_56, '#skF_6'('#skF_7', k1_relat_1('#skF_8'), C_56)), B_77) | ~r1_tarski('#skF_7', B_77) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_56, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_75, c_173])).
% 5.94/2.14  tff(c_413, plain, (![C_94, B_95]: (r2_hidden(k4_tarski(C_94, '#skF_6'('#skF_7', k1_relat_1('#skF_8'), C_94)), B_95) | ~r1_tarski('#skF_7', B_95) | ~r2_hidden(C_94, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_177])).
% 5.94/2.14  tff(c_444, plain, (![C_94, B_95]: (r2_hidden(C_94, k1_relat_1(B_95)) | ~r1_tarski('#skF_7', B_95) | ~r2_hidden(C_94, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_413, c_16])).
% 5.94/2.14  tff(c_629, plain, (![A_110, B_111, B_95]: (r2_hidden('#skF_1'(A_110, B_111), k1_relat_1(B_95)) | ~r1_tarski('#skF_7', B_95) | ~r1_tarski(A_110, '#skF_8') | r1_tarski(A_110, B_111) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_612, c_444])).
% 5.94/2.14  tff(c_609, plain, (![B_109, A_107, B_108]: (k1_funct_1(B_109, '#skF_1'(A_107, B_108))='#skF_2'(A_107, B_108) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109) | ~r1_tarski(A_107, B_109) | r1_tarski(A_107, B_108) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_577, c_28])).
% 5.94/2.14  tff(c_126, plain, (![B_66]: (k1_funct_1('#skF_7', '#skF_1'('#skF_8', B_66))=k1_funct_1('#skF_8', '#skF_1'('#skF_8', B_66)) | r1_tarski('#skF_8', B_66) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_118, c_45])).
% 5.94/2.14  tff(c_135, plain, (![B_66]: (k1_funct_1('#skF_7', '#skF_1'('#skF_8', B_66))=k1_funct_1('#skF_8', '#skF_1'('#skF_8', B_66)) | r1_tarski('#skF_8', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_126])).
% 5.94/2.14  tff(c_185, plain, (![A_79, C_80]: (r2_hidden(k4_tarski(A_79, k1_funct_1(C_80, A_79)), C_80) | ~r2_hidden(A_79, k1_relat_1(C_80)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.94/2.14  tff(c_207, plain, (![B_66]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', B_66), k1_funct_1('#skF_8', '#skF_1'('#skF_8', B_66))), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', B_66), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | r1_tarski('#skF_8', B_66))), inference(superposition, [status(thm), theory('equality')], [c_135, c_185])).
% 5.94/2.14  tff(c_2458, plain, (![B_194]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', B_194), k1_funct_1('#skF_8', '#skF_1'('#skF_8', B_194))), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', B_194), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', B_194))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_207])).
% 5.94/2.14  tff(c_2474, plain, (![B_108]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', B_108), '#skF_2'('#skF_8', B_108)), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', B_108), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', B_108) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', B_108) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_609, c_2458])).
% 5.94/2.14  tff(c_2493, plain, (![B_195]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', B_195), '#skF_2'('#skF_8', B_195)), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', B_195), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', B_195))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_40, c_38, c_2474])).
% 5.94/2.14  tff(c_2499, plain, (~v1_relat_1('#skF_8') | ~r2_hidden('#skF_1'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_2493, c_10])).
% 5.94/2.14  tff(c_2511, plain, (~r2_hidden('#skF_1'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2499])).
% 5.94/2.14  tff(c_2512, plain, (~r2_hidden('#skF_1'('#skF_8', '#skF_7'), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1436, c_2511])).
% 5.94/2.14  tff(c_2520, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_629, c_2512])).
% 5.94/2.14  tff(c_2541, plain, (r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_1396, c_2520])).
% 5.94/2.14  tff(c_2543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1436, c_2541])).
% 5.94/2.14  tff(c_2544, plain, (r1_tarski('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_1364])).
% 5.94/2.14  tff(c_2549, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_2544, c_2])).
% 5.94/2.14  tff(c_2555, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_2549])).
% 5.94/2.14  tff(c_5012, plain, (![B_254]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', B_254), k1_funct_1('#skF_8', '#skF_1'('#skF_8', B_254))), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', B_254), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', B_254))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_207])).
% 5.94/2.14  tff(c_5028, plain, (![B_108]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', B_108), '#skF_2'('#skF_8', B_108)), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', B_108), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', B_108) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', B_108) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_609, c_5012])).
% 5.94/2.14  tff(c_5047, plain, (![B_255]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', B_255), '#skF_2'('#skF_8', B_255)), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', B_255), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', B_255))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_40, c_38, c_5028])).
% 5.94/2.14  tff(c_5053, plain, (~v1_relat_1('#skF_8') | ~r2_hidden('#skF_1'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_5047, c_10])).
% 5.94/2.14  tff(c_5065, plain, (~r2_hidden('#skF_1'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5053])).
% 5.94/2.14  tff(c_5066, plain, (~r2_hidden('#skF_1'('#skF_8', '#skF_7'), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2555, c_5065])).
% 5.94/2.14  tff(c_5074, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_629, c_5066])).
% 5.94/2.14  tff(c_5095, plain, (r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_2544, c_5074])).
% 5.94/2.14  tff(c_5097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2555, c_5095])).
% 5.94/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.14  
% 5.94/2.14  Inference rules
% 5.94/2.14  ----------------------
% 5.94/2.14  #Ref     : 0
% 5.94/2.14  #Sup     : 977
% 5.94/2.14  #Fact    : 0
% 5.94/2.14  #Define  : 0
% 5.94/2.14  #Split   : 5
% 5.94/2.14  #Chain   : 0
% 5.94/2.14  #Close   : 0
% 5.94/2.14  
% 5.94/2.14  Ordering : KBO
% 5.94/2.14  
% 5.94/2.14  Simplification rules
% 5.94/2.14  ----------------------
% 5.94/2.14  #Subsume      : 198
% 5.94/2.14  #Demod        : 1146
% 5.94/2.14  #Tautology    : 368
% 5.94/2.14  #SimpNegUnit  : 6
% 5.94/2.14  #BackRed      : 0
% 5.94/2.14  
% 5.94/2.14  #Partial instantiations: 0
% 6.09/2.14  #Strategies tried      : 1
% 6.09/2.14  
% 6.09/2.14  Timing (in seconds)
% 6.09/2.14  ----------------------
% 6.09/2.14  Preprocessing        : 0.29
% 6.09/2.14  Parsing              : 0.14
% 6.09/2.14  CNF conversion       : 0.03
% 6.09/2.14  Main loop            : 1.04
% 6.09/2.14  Inferencing          : 0.38
% 6.09/2.14  Reduction            : 0.32
% 6.09/2.14  Demodulation         : 0.21
% 6.09/2.14  BG Simplification    : 0.05
% 6.09/2.14  Subsumption          : 0.22
% 6.09/2.14  Abstraction          : 0.07
% 6.09/2.14  MUC search           : 0.00
% 6.09/2.14  Cooper               : 0.00
% 6.09/2.14  Total                : 1.36
% 6.09/2.14  Index Insertion      : 0.00
% 6.09/2.14  Index Deletion       : 0.00
% 6.09/2.14  Index Matching       : 0.00
% 6.09/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
