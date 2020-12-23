%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:37 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :  167 (2360 expanded)
%              Number of leaves         :   25 ( 719 expanded)
%              Depth                    :   21
%              Number of atoms          :  376 (7753 expanded)
%              Number of equality atoms :  158 (3796 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( B = k6_relat_1(A)
        <=> ( k1_relat_1(B) = A
            & ! [C] :
                ( r2_hidden(C,A)
               => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,
    ( k6_relat_1('#skF_5') = '#skF_6'
    | k1_relat_1('#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_86,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_111,plain,(
    ! [A_34,B_35] :
      ( k1_funct_1(A_34,B_35) = k1_xboole_0
      | r2_hidden(B_35,k1_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    ! [B_35] :
      ( k1_funct_1('#skF_6',B_35) = k1_xboole_0
      | r2_hidden(B_35,'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_111])).

tff(c_122,plain,(
    ! [B_36] :
      ( k1_funct_1('#skF_6',B_36) = k1_xboole_0
      | r2_hidden(B_36,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_114])).

tff(c_48,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | k1_relat_1('#skF_6') != '#skF_5'
    | k6_relat_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_93,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | k6_relat_1('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_48])).

tff(c_94,plain,(
    k6_relat_1('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_50,plain,(
    ! [C_21] :
      ( k6_relat_1('#skF_5') = '#skF_6'
      | k1_funct_1('#skF_6',C_21) = C_21
      | ~ r2_hidden(C_21,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_109,plain,(
    ! [C_21] :
      ( k1_funct_1('#skF_6',C_21) = C_21
      | ~ r2_hidden(C_21,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_50])).

tff(c_126,plain,(
    ! [B_36] :
      ( k1_funct_1('#skF_6',B_36) = B_36
      | k1_funct_1('#skF_6',B_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_122,c_109])).

tff(c_135,plain,(
    ! [B_36] :
      ( k1_funct_1('#skF_6',B_36) = B_36
      | k1_xboole_0 != B_36 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_126])).

tff(c_349,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r2_hidden(k4_tarski('#skF_3'(A_55,B_56),'#skF_4'(A_55,B_56)),B_56)
      | k6_relat_1(A_55) = B_56
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(A_16,k1_relat_1(C_18))
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_413,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_3'(A_61,B_62),k1_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | r2_hidden('#skF_1'(A_61,B_62),A_61)
      | k6_relat_1(A_61) = B_62
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_349,c_38])).

tff(c_418,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_3'(A_61,'#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | r2_hidden('#skF_1'(A_61,'#skF_6'),A_61)
      | k6_relat_1(A_61) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_413])).

tff(c_423,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_3'(A_61,'#skF_6'),'#skF_5')
      | r2_hidden('#skF_1'(A_61,'#skF_6'),A_61)
      | k6_relat_1(A_61) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_418])).

tff(c_1174,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,B_100),A_99)
      | '#skF_3'(A_99,B_100) != '#skF_4'(A_99,B_100)
      | ~ r2_hidden('#skF_3'(A_99,B_100),A_99)
      | k6_relat_1(A_99) = B_100
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1196,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_6')
    | r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_423,c_1174])).

tff(c_1230,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1196])).

tff(c_1231,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1230])).

tff(c_1239,plain,(
    '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1231])).

tff(c_426,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_3'(A_63,'#skF_6'),'#skF_5')
      | r2_hidden('#skF_1'(A_63,'#skF_6'),A_63)
      | k6_relat_1(A_63) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_418])).

tff(c_433,plain,(
    ! [A_64] :
      ( k1_funct_1('#skF_6','#skF_3'(A_64,'#skF_6')) = '#skF_3'(A_64,'#skF_6')
      | r2_hidden('#skF_1'(A_64,'#skF_6'),A_64)
      | k6_relat_1(A_64) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_426,c_109])).

tff(c_437,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_433,c_109])).

tff(c_440,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_437])).

tff(c_448,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_36,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_369,plain,(
    ! [B_56,A_55] :
      ( k1_funct_1(B_56,'#skF_3'(A_55,B_56)) = '#skF_4'(A_55,B_56)
      | ~ v1_funct_1(B_56)
      | r2_hidden('#skF_1'(A_55,B_56),A_55)
      | k6_relat_1(A_55) = B_56
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_349,c_36])).

tff(c_1282,plain,(
    ! [B_102,A_103] :
      ( k1_funct_1(B_102,'#skF_3'(A_103,B_102)) = '#skF_4'(A_103,B_102)
      | ~ v1_funct_1(B_102)
      | r2_hidden('#skF_1'(A_103,B_102),A_103)
      | k6_relat_1(A_103) = B_102
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_349,c_36])).

tff(c_1626,plain,(
    ! [B_110] :
      ( k1_funct_1('#skF_6','#skF_1'('#skF_5',B_110)) = '#skF_1'('#skF_5',B_110)
      | k1_funct_1(B_110,'#skF_3'('#skF_5',B_110)) = '#skF_4'('#skF_5',B_110)
      | ~ v1_funct_1(B_110)
      | k6_relat_1('#skF_5') = B_110
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_1282,c_109])).

tff(c_1659,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_448])).

tff(c_1742,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1659])).

tff(c_1743,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1239,c_1742])).

tff(c_34,plain,(
    ! [A_16,C_18] :
      ( r2_hidden(k4_tarski(A_16,k1_funct_1(C_18,A_16)),C_18)
      | ~ r2_hidden(A_16,k1_relat_1(C_18))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1784,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1743,c_34])).

tff(c_1809,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_86,c_1784])).

tff(c_1860,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1809])).

tff(c_1863,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_369,c_1860])).

tff(c_1874,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_448,c_1863])).

tff(c_1876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1239,c_1874])).

tff(c_1877,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_385,plain,(
    ! [A_59,B_60] :
      ( '#skF_2'(A_59,B_60) = '#skF_1'(A_59,B_60)
      | r2_hidden(k4_tarski('#skF_3'(A_59,B_60),'#skF_4'(A_59,B_60)),B_60)
      | k6_relat_1(A_59) = B_60
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1320,plain,(
    ! [B_104,A_105] :
      ( k1_funct_1(B_104,'#skF_3'(A_105,B_104)) = '#skF_4'(A_105,B_104)
      | ~ v1_funct_1(B_104)
      | '#skF_2'(A_105,B_104) = '#skF_1'(A_105,B_104)
      | k6_relat_1(A_105) = B_104
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_385,c_36])).

tff(c_1333,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1320,c_448])).

tff(c_1384,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1333])).

tff(c_1385,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1239,c_1384])).

tff(c_1821,plain,(
    ! [A_111,B_112] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_111,B_112),'#skF_2'(A_111,B_112)),B_112)
      | r2_hidden(k4_tarski('#skF_3'(A_111,B_112),'#skF_4'(A_111,B_112)),B_112)
      | k6_relat_1(A_111) = B_112
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3007,plain,(
    ! [B_1172,A_1173] :
      ( k1_funct_1(B_1172,'#skF_3'(A_1173,B_1172)) = '#skF_4'(A_1173,B_1172)
      | ~ v1_funct_1(B_1172)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_1173,B_1172),'#skF_2'(A_1173,B_1172)),B_1172)
      | k6_relat_1(A_1173) = B_1172
      | ~ v1_relat_1(B_1172) ) ),
    inference(resolution,[status(thm)],[c_1821,c_36])).

tff(c_3014,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1385,c_3007])).

tff(c_3025,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1877,c_40,c_448,c_3014])).

tff(c_3027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1239,c_3025])).

tff(c_3029,plain,(
    '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1231])).

tff(c_119,plain,(
    ! [B_35] :
      ( k1_funct_1('#skF_6',B_35) = k1_xboole_0
      | r2_hidden(B_35,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_114])).

tff(c_452,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6'),'#skF_3'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_34])).

tff(c_476,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6'),'#skF_3'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_86,c_452])).

tff(c_484,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_494,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_119,c_484])).

tff(c_531,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_448])).

tff(c_566,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_484])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( '#skF_2'(A_1,B_2) = '#skF_1'(A_1,B_2)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2),'#skF_4'(A_1,B_2)),B_2)
      | k6_relat_1(A_1) = B_2
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_580,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | r2_hidden(k4_tarski(k1_xboole_0,'#skF_4'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_10])).

tff(c_595,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | r2_hidden(k4_tarski(k1_xboole_0,'#skF_4'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_580])).

tff(c_596,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | r2_hidden(k4_tarski(k1_xboole_0,'#skF_4'('#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_595])).

tff(c_653,plain,(
    r2_hidden(k4_tarski(k1_xboole_0,'#skF_4'('#skF_5','#skF_6')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_656,plain,
    ( r2_hidden(k1_xboole_0,k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_653,c_38])).

tff(c_662,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_86,c_656])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_662])).

tff(c_666,plain,(
    ~ r2_hidden(k4_tarski(k1_xboole_0,'#skF_4'('#skF_5','#skF_6')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_487,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_423,c_484])).

tff(c_493,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_487])).

tff(c_498,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_493,c_109])).

tff(c_609,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_34])).

tff(c_633,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_493,c_86,c_609])).

tff(c_665,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_966,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_86,B_87),'#skF_2'(A_86,B_87)),B_87)
      | r2_hidden(k4_tarski('#skF_3'(A_86,B_87),'#skF_4'(A_86,B_87)),B_87)
      | k6_relat_1(A_86) = B_87
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_990,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_2'('#skF_5','#skF_6')),'#skF_6')
    | r2_hidden(k4_tarski(k1_xboole_0,'#skF_4'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_966])).

tff(c_1003,plain,
    ( r2_hidden(k4_tarski(k1_xboole_0,'#skF_4'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_633,c_665,c_990])).

tff(c_1005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_666,c_1003])).

tff(c_1007,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_3035,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3029,c_1007])).

tff(c_3028,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1231])).

tff(c_3033,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3028,c_109])).

tff(c_3092,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3033,c_34])).

tff(c_3116,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3028,c_86,c_3092])).

tff(c_1075,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_3'(A_93,B_94),k1_relat_1(B_94))
      | ~ v1_funct_1(B_94)
      | '#skF_2'(A_93,B_94) = '#skF_1'(A_93,B_94)
      | k6_relat_1(A_93) = B_94
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_385,c_38])).

tff(c_1078,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_3'(A_93,'#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | '#skF_2'(A_93,'#skF_6') = '#skF_1'(A_93,'#skF_6')
      | k6_relat_1(A_93) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1075])).

tff(c_1083,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_3'(A_93,'#skF_6'),'#skF_5')
      | '#skF_2'(A_93,'#skF_6') = '#skF_1'(A_93,'#skF_6')
      | k6_relat_1(A_93) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1078])).

tff(c_3185,plain,(
    ! [A_1174,B_1175] :
      ( '#skF_2'(A_1174,B_1175) = '#skF_1'(A_1174,B_1175)
      | '#skF_3'(A_1174,B_1175) != '#skF_4'(A_1174,B_1175)
      | ~ r2_hidden('#skF_3'(A_1174,B_1175),A_1174)
      | k6_relat_1(A_1174) = B_1175
      | ~ v1_relat_1(B_1175) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3195,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1083,c_3185])).

tff(c_3231,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3029,c_3195])).

tff(c_3232,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3231])).

tff(c_4067,plain,(
    ! [A_2093,B_2094] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_2093,B_2094),'#skF_2'(A_2093,B_2094)),B_2094)
      | '#skF_3'(A_2093,B_2094) != '#skF_4'(A_2093,B_2094)
      | ~ r2_hidden('#skF_3'(A_2093,B_2094),A_2093)
      | k6_relat_1(A_2093) = B_2094
      | ~ v1_relat_1(B_2094) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4077,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3232,c_4067])).

tff(c_4088,plain,(
    k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3035,c_3029,c_3029,c_3116,c_4077])).

tff(c_4090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4088])).

tff(c_4092,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_4138,plain,(
    '#skF_3'('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_4092])).

tff(c_4139,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_4092])).

tff(c_4144,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6'),k1_xboole_0),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4139,c_34])).

tff(c_4168,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6'),k1_xboole_0),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_86,c_4144])).

tff(c_4176,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4168])).

tff(c_4179,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_423,c_4176])).

tff(c_4185,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4179])).

tff(c_4091,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_4096,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4091,c_34])).

tff(c_4120,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_86,c_4096])).

tff(c_4194,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4185,c_4120])).

tff(c_4259,plain,(
    ! [A_2116,B_2117] :
      ( r2_hidden('#skF_3'(A_2116,B_2117),k1_relat_1(B_2117))
      | ~ v1_funct_1(B_2117)
      | '#skF_2'(A_2116,B_2117) = '#skF_1'(A_2116,B_2117)
      | k6_relat_1(A_2116) = B_2117
      | ~ v1_relat_1(B_2117) ) ),
    inference(resolution,[status(thm)],[c_385,c_38])).

tff(c_4266,plain,(
    ! [A_2116] :
      ( r2_hidden('#skF_3'(A_2116,'#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | '#skF_2'(A_2116,'#skF_6') = '#skF_1'(A_2116,'#skF_6')
      | k6_relat_1(A_2116) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_4259])).

tff(c_4313,plain,(
    ! [A_2119] :
      ( r2_hidden('#skF_3'(A_2119,'#skF_6'),'#skF_5')
      | '#skF_2'(A_2119,'#skF_6') = '#skF_1'(A_2119,'#skF_6')
      | k6_relat_1(A_2119) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4266])).

tff(c_4320,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4313,c_4176])).

tff(c_4330,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4320])).

tff(c_5063,plain,(
    ! [A_3006,B_3007] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3006,B_3007),'#skF_2'(A_3006,B_3007)),B_3007)
      | r2_hidden(k4_tarski('#skF_3'(A_3006,B_3007),'#skF_4'(A_3006,B_3007)),B_3007)
      | k6_relat_1(A_3006) = B_3007
      | ~ v1_relat_1(B_3007) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5637,plain,(
    ! [A_3088,B_3089] :
      ( r2_hidden('#skF_3'(A_3088,B_3089),k1_relat_1(B_3089))
      | ~ v1_funct_1(B_3089)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_3088,B_3089),'#skF_2'(A_3088,B_3089)),B_3089)
      | k6_relat_1(A_3088) = B_3089
      | ~ v1_relat_1(B_3089) ) ),
    inference(resolution,[status(thm)],[c_5063,c_38])).

tff(c_5644,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4330,c_5637])).

tff(c_5655,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4194,c_40,c_86,c_5644])).

tff(c_5657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4176,c_5655])).

tff(c_5659,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4168])).

tff(c_5662,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_5659,c_109])).

tff(c_5664,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4139,c_5662])).

tff(c_5666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4138,c_5664])).

tff(c_5668,plain,(
    k6_relat_1('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_46,plain,
    ( k1_funct_1('#skF_6','#skF_7') != '#skF_7'
    | k1_relat_1('#skF_6') != '#skF_5'
    | k6_relat_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5686,plain,(
    k1_funct_1('#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5668,c_86,c_46])).

tff(c_5667,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_28,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5692,plain,(
    ! [D_3092,A_3093] :
      ( r2_hidden(k4_tarski(D_3092,D_3092),k6_relat_1(A_3093))
      | ~ r2_hidden(D_3092,A_3093) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_5698,plain,(
    ! [D_3092] :
      ( r2_hidden(k4_tarski(D_3092,D_3092),'#skF_6')
      | ~ r2_hidden(D_3092,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5668,c_5692])).

tff(c_5763,plain,(
    ! [C_3108,A_3109,B_3110] :
      ( k1_funct_1(C_3108,A_3109) = B_3110
      | ~ r2_hidden(k4_tarski(A_3109,B_3110),C_3108)
      | ~ v1_funct_1(C_3108)
      | ~ v1_relat_1(C_3108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5774,plain,(
    ! [D_3092] :
      ( k1_funct_1('#skF_6',D_3092) = D_3092
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_3092,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5698,c_5763])).

tff(c_5786,plain,(
    ! [D_3111] :
      ( k1_funct_1('#skF_6',D_3111) = D_3111
      | ~ r2_hidden(D_3111,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5774])).

tff(c_5792,plain,(
    k1_funct_1('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5667,c_5786])).

tff(c_5797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5686,c_5792])).

tff(c_5799,plain,(
    k1_relat_1('#skF_6') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5798,plain,(
    k6_relat_1('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_30,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5806,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5798,c_30])).

tff(c_5813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5799,c_5806])).

%------------------------------------------------------------------------------
