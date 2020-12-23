%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:18 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  153 (1756 expanded)
%              Number of leaves         :   23 ( 538 expanded)
%              Depth                    :   19
%              Number of atoms          :  364 (5781 expanded)
%              Number of equality atoms :  157 (2828 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( B = k6_relat_1(A)
        <=> ( k1_relat_1(B) = A
            & ! [C] :
                ( r2_hidden(C,A)
               => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(c_50,plain,
    ( k6_relat_1('#skF_5') = '#skF_6'
    | k1_relat_1('#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_42,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | k1_relat_1('#skF_6') != '#skF_5'
    | k6_relat_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | k6_relat_1('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_42])).

tff(c_89,plain,(
    k6_relat_1('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_166,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r2_hidden(k4_tarski('#skF_3'(A_40,B_41),'#skF_4'(A_40,B_41)),B_41)
      | k6_relat_1(A_40) = B_41
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    ! [A_11,C_13,B_12] :
      ( r2_hidden(A_11,k1_relat_1(C_13))
      | ~ r2_hidden(k4_tarski(A_11,B_12),C_13)
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_202,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_3'(A_44,B_45),k1_relat_1(B_45))
      | ~ v1_funct_1(B_45)
      | r2_hidden('#skF_1'(A_44,B_45),A_44)
      | k6_relat_1(A_44) = B_45
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_166,c_32])).

tff(c_207,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'(A_44,'#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | r2_hidden('#skF_1'(A_44,'#skF_6'),A_44)
      | k6_relat_1(A_44) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_202])).

tff(c_212,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'(A_44,'#skF_6'),'#skF_5')
      | r2_hidden('#skF_1'(A_44,'#skF_6'),A_44)
      | k6_relat_1(A_44) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_207])).

tff(c_1243,plain,(
    ! [A_863,B_864] :
      ( r2_hidden('#skF_1'(A_863,B_864),A_863)
      | '#skF_3'(A_863,B_864) != '#skF_4'(A_863,B_864)
      | ~ r2_hidden('#skF_3'(A_863,B_864),A_863)
      | k6_relat_1(A_863) = B_864
      | ~ v1_relat_1(B_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1265,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_6')
    | r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_212,c_1243])).

tff(c_1291,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1265])).

tff(c_1292,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1291])).

tff(c_1298,plain,(
    '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1292])).

tff(c_215,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_3'(A_46,'#skF_6'),'#skF_5')
      | r2_hidden('#skF_1'(A_46,'#skF_6'),A_46)
      | k6_relat_1(A_46) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_207])).

tff(c_44,plain,(
    ! [C_16] :
      ( k6_relat_1('#skF_5') = '#skF_6'
      | k1_funct_1('#skF_6',C_16) = C_16
      | ~ r2_hidden(C_16,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_101,plain,(
    ! [C_16] :
      ( k1_funct_1('#skF_6',C_16) = C_16
      | ~ r2_hidden(C_16,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_44])).

tff(c_250,plain,(
    ! [A_49] :
      ( k1_funct_1('#skF_6','#skF_3'(A_49,'#skF_6')) = '#skF_3'(A_49,'#skF_6')
      | r2_hidden('#skF_1'(A_49,'#skF_6'),A_49)
      | k6_relat_1(A_49) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_215,c_101])).

tff(c_254,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_250,c_101])).

tff(c_257,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_254])).

tff(c_258,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_30,plain,(
    ! [C_13,A_11,B_12] :
      ( k1_funct_1(C_13,A_11) = B_12
      | ~ r2_hidden(k4_tarski(A_11,B_12),C_13)
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_186,plain,(
    ! [B_41,A_40] :
      ( k1_funct_1(B_41,'#skF_3'(A_40,B_41)) = '#skF_4'(A_40,B_41)
      | ~ v1_funct_1(B_41)
      | r2_hidden('#skF_1'(A_40,B_41),A_40)
      | k6_relat_1(A_40) = B_41
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_166,c_30])).

tff(c_222,plain,(
    ! [A_47,B_48] :
      ( '#skF_2'(A_47,B_48) = '#skF_1'(A_47,B_48)
      | r2_hidden(k4_tarski('#skF_3'(A_47,B_48),'#skF_4'(A_47,B_48)),B_48)
      | k6_relat_1(A_47) = B_48
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1358,plain,(
    ! [B_870,A_871] :
      ( k1_funct_1(B_870,'#skF_3'(A_871,B_870)) = '#skF_4'(A_871,B_870)
      | ~ v1_funct_1(B_870)
      | '#skF_2'(A_871,B_870) = '#skF_1'(A_871,B_870)
      | k6_relat_1(A_871) = B_870
      | ~ v1_relat_1(B_870) ) ),
    inference(resolution,[status(thm)],[c_222,c_30])).

tff(c_1371,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_258])).

tff(c_1403,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1371])).

tff(c_1404,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1298,c_1403])).

tff(c_1847,plain,(
    ! [A_1600,B_1601] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1600,B_1601),'#skF_2'(A_1600,B_1601)),B_1601)
      | r2_hidden(k4_tarski('#skF_3'(A_1600,B_1601),'#skF_4'(A_1600,B_1601)),B_1601)
      | k6_relat_1(A_1600) = B_1601
      | ~ v1_relat_1(B_1601) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2065,plain,(
    ! [B_1630,A_1631] :
      ( k1_funct_1(B_1630,'#skF_3'(A_1631,B_1630)) = '#skF_4'(A_1631,B_1630)
      | ~ v1_funct_1(B_1630)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_1631,B_1630),'#skF_2'(A_1631,B_1630)),B_1630)
      | k6_relat_1(A_1631) = B_1630
      | ~ v1_relat_1(B_1630) ) ),
    inference(resolution,[status(thm)],[c_1847,c_30])).

tff(c_2068,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_2065])).

tff(c_2070,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_258,c_2068])).

tff(c_2071,plain,(
    ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1298,c_2070])).

tff(c_1319,plain,(
    ! [B_868,A_869] :
      ( k1_funct_1(B_868,'#skF_3'(A_869,B_868)) = '#skF_4'(A_869,B_868)
      | ~ v1_funct_1(B_868)
      | r2_hidden('#skF_1'(A_869,B_868),A_869)
      | k6_relat_1(A_869) = B_868
      | ~ v1_relat_1(B_868) ) ),
    inference(resolution,[status(thm)],[c_166,c_30])).

tff(c_2095,plain,(
    ! [B_1634] :
      ( k1_funct_1('#skF_6','#skF_1'('#skF_5',B_1634)) = '#skF_1'('#skF_5',B_1634)
      | k1_funct_1(B_1634,'#skF_3'('#skF_5',B_1634)) = '#skF_4'('#skF_5',B_1634)
      | ~ v1_funct_1(B_1634)
      | k6_relat_1('#skF_5') = B_1634
      | ~ v1_relat_1(B_1634) ) ),
    inference(resolution,[status(thm)],[c_1319,c_101])).

tff(c_2118,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2095,c_258])).

tff(c_2170,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2118])).

tff(c_2171,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1298,c_2170])).

tff(c_28,plain,(
    ! [A_11,C_13] :
      ( r2_hidden(k4_tarski(A_11,k1_funct_1(C_13,A_11)),C_13)
      | ~ r2_hidden(A_11,k1_relat_1(C_13))
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2195,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_28])).

tff(c_2200,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_81,c_2195])).

tff(c_2201,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2071,c_2200])).

tff(c_2205,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_4'('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_186,c_2201])).

tff(c_2213,plain,
    ( '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_258,c_2205])).

tff(c_2215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1298,c_2213])).

tff(c_2217,plain,(
    '#skF_3'('#skF_5','#skF_6') = '#skF_4'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1292])).

tff(c_262,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6'),'#skF_3'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_28])).

tff(c_266,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6'),'#skF_3'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_81,c_262])).

tff(c_269,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_272,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_212,c_269])).

tff(c_275,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_272])).

tff(c_279,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_275,c_101])).

tff(c_283,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_28])).

tff(c_287,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_275,c_81,c_283])).

tff(c_350,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_3'(A_57,B_58),k1_relat_1(B_58))
      | ~ v1_funct_1(B_58)
      | '#skF_2'(A_57,B_58) = '#skF_1'(A_57,B_58)
      | k6_relat_1(A_57) = B_58
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_222,c_32])).

tff(c_357,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_3'(A_57,'#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | '#skF_2'(A_57,'#skF_6') = '#skF_1'(A_57,'#skF_6')
      | k6_relat_1(A_57) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_350])).

tff(c_366,plain,(
    ! [A_59] :
      ( r2_hidden('#skF_3'(A_59,'#skF_6'),'#skF_5')
      | '#skF_2'(A_59,'#skF_6') = '#skF_1'(A_59,'#skF_6')
      | k6_relat_1(A_59) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_357])).

tff(c_373,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_366,c_269])).

tff(c_383,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_373])).

tff(c_932,plain,(
    ! [A_809,B_810] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_809,B_810),'#skF_2'(A_809,B_810)),B_810)
      | r2_hidden(k4_tarski('#skF_3'(A_809,B_810),'#skF_4'(A_809,B_810)),B_810)
      | k6_relat_1(A_809) = B_810
      | ~ v1_relat_1(B_810) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1122,plain,(
    ! [A_850,B_851] :
      ( r2_hidden('#skF_3'(A_850,B_851),k1_relat_1(B_851))
      | ~ v1_funct_1(B_851)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_850,B_851),'#skF_2'(A_850,B_851)),B_851)
      | k6_relat_1(A_850) = B_851
      | ~ v1_relat_1(B_851) ) ),
    inference(resolution,[status(thm)],[c_932,c_32])).

tff(c_1125,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_1122])).

tff(c_1127,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_287,c_34,c_81,c_1125])).

tff(c_1129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_269,c_1127])).

tff(c_1131,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_2223,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2217,c_1131])).

tff(c_2216,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1292])).

tff(c_2221,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2216,c_101])).

tff(c_2339,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2221,c_28])).

tff(c_2343,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2216,c_81,c_2339])).

tff(c_1168,plain,(
    ! [A_857,B_858] :
      ( r2_hidden('#skF_3'(A_857,B_858),k1_relat_1(B_858))
      | ~ v1_funct_1(B_858)
      | '#skF_2'(A_857,B_858) = '#skF_1'(A_857,B_858)
      | k6_relat_1(A_857) = B_858
      | ~ v1_relat_1(B_858) ) ),
    inference(resolution,[status(thm)],[c_222,c_32])).

tff(c_1171,plain,(
    ! [A_857] :
      ( r2_hidden('#skF_3'(A_857,'#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | '#skF_2'(A_857,'#skF_6') = '#skF_1'(A_857,'#skF_6')
      | k6_relat_1(A_857) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_1168])).

tff(c_1176,plain,(
    ! [A_857] :
      ( r2_hidden('#skF_3'(A_857,'#skF_6'),'#skF_5')
      | '#skF_2'(A_857,'#skF_6') = '#skF_1'(A_857,'#skF_6')
      | k6_relat_1(A_857) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1171])).

tff(c_2277,plain,(
    ! [A_1635,B_1636] :
      ( '#skF_2'(A_1635,B_1636) = '#skF_1'(A_1635,B_1636)
      | '#skF_3'(A_1635,B_1636) != '#skF_4'(A_1635,B_1636)
      | ~ r2_hidden('#skF_3'(A_1635,B_1636),A_1635)
      | k6_relat_1(A_1635) = B_1636
      | ~ v1_relat_1(B_1636) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2287,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1176,c_2277])).

tff(c_2315,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2217,c_2287])).

tff(c_2316,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_2315])).

tff(c_2539,plain,(
    ! [A_1646,B_1647] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1646,B_1647),'#skF_2'(A_1646,B_1647)),B_1647)
      | '#skF_3'(A_1646,B_1647) != '#skF_4'(A_1646,B_1647)
      | ~ r2_hidden('#skF_3'(A_1646,B_1647),A_1646)
      | k6_relat_1(A_1646) = B_1647
      | ~ v1_relat_1(B_1647) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2542,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2316,c_2539])).

tff(c_2544,plain,(
    k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2223,c_2217,c_2217,c_2343,c_2542])).

tff(c_2546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_2544])).

tff(c_2548,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) != '#skF_3'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_221,plain,(
    ! [A_46] :
      ( k1_funct_1('#skF_6','#skF_3'(A_46,'#skF_6')) = '#skF_3'(A_46,'#skF_6')
      | r2_hidden('#skF_1'(A_46,'#skF_6'),A_46)
      | k6_relat_1(A_46) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_215,c_101])).

tff(c_2547,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_6')) = '#skF_1'('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_2552,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2547,c_28])).

tff(c_2556,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_81,c_2552])).

tff(c_2558,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2556])).

tff(c_2562,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_221,c_2558])).

tff(c_2568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_2548,c_2562])).

tff(c_2569,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2556])).

tff(c_2630,plain,(
    ! [A_1654,B_1655] :
      ( r2_hidden('#skF_3'(A_1654,B_1655),k1_relat_1(B_1655))
      | ~ v1_funct_1(B_1655)
      | '#skF_2'(A_1654,B_1655) = '#skF_1'(A_1654,B_1655)
      | k6_relat_1(A_1654) = B_1655
      | ~ v1_relat_1(B_1655) ) ),
    inference(resolution,[status(thm)],[c_222,c_32])).

tff(c_2637,plain,(
    ! [A_1654] :
      ( r2_hidden('#skF_3'(A_1654,'#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | '#skF_2'(A_1654,'#skF_6') = '#skF_1'(A_1654,'#skF_6')
      | k6_relat_1(A_1654) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_2630])).

tff(c_2646,plain,(
    ! [A_1656] :
      ( r2_hidden('#skF_3'(A_1656,'#skF_6'),'#skF_5')
      | '#skF_2'(A_1656,'#skF_6') = '#skF_1'(A_1656,'#skF_6')
      | k6_relat_1(A_1656) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2637])).

tff(c_2659,plain,(
    ! [A_1657] :
      ( k1_funct_1('#skF_6','#skF_3'(A_1657,'#skF_6')) = '#skF_3'(A_1657,'#skF_6')
      | '#skF_2'(A_1657,'#skF_6') = '#skF_1'(A_1657,'#skF_6')
      | k6_relat_1(A_1657) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2646,c_101])).

tff(c_2665,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2659,c_2548])).

tff(c_2675,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_1'('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_2665])).

tff(c_3366,plain,(
    ! [A_2402,B_2403] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_2402,B_2403),'#skF_2'(A_2402,B_2403)),B_2403)
      | '#skF_3'(A_2402,B_2403) != '#skF_4'(A_2402,B_2403)
      | ~ r2_hidden('#skF_3'(A_2402,B_2403),A_2402)
      | k6_relat_1(A_2402) = B_2403
      | ~ v1_relat_1(B_2403) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3369,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2675,c_3366])).

tff(c_3371,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2569,c_3369])).

tff(c_3372,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_4'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_3371])).

tff(c_3373,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3372])).

tff(c_3195,plain,(
    ! [A_2364,B_2365] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_2364,B_2365),'#skF_2'(A_2364,B_2365)),B_2365)
      | r2_hidden(k4_tarski('#skF_3'(A_2364,B_2365),'#skF_4'(A_2364,B_2365)),B_2365)
      | k6_relat_1(A_2364) = B_2365
      | ~ v1_relat_1(B_2365) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3398,plain,(
    ! [A_2405,B_2406] :
      ( r2_hidden('#skF_3'(A_2405,B_2406),k1_relat_1(B_2406))
      | ~ v1_funct_1(B_2406)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_2405,B_2406),'#skF_2'(A_2405,B_2406)),B_2406)
      | k6_relat_1(A_2405) = B_2406
      | ~ v1_relat_1(B_2406) ) ),
    inference(resolution,[status(thm)],[c_3195,c_32])).

tff(c_3401,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_1'('#skF_5','#skF_6')),'#skF_6')
    | k6_relat_1('#skF_5') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2675,c_3398])).

tff(c_3403,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2569,c_34,c_81,c_3401])).

tff(c_3405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_3373,c_3403])).

tff(c_3407,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3372])).

tff(c_3416,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_6')) = '#skF_3'('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3407,c_101])).

tff(c_3431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2548,c_3416])).

tff(c_3433,plain,(
    k6_relat_1('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_40,plain,
    ( k1_funct_1('#skF_6','#skF_7') != '#skF_7'
    | k1_relat_1('#skF_6') != '#skF_5'
    | k6_relat_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3483,plain,(
    k1_funct_1('#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3433,c_81,c_40])).

tff(c_3432,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_24,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3459,plain,(
    ! [D_2409,A_2410] :
      ( r2_hidden(k4_tarski(D_2409,D_2409),k6_relat_1(A_2410))
      | ~ r2_hidden(D_2409,A_2410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14])).

tff(c_3465,plain,(
    ! [D_2409] :
      ( r2_hidden(k4_tarski(D_2409,D_2409),'#skF_6')
      | ~ r2_hidden(D_2409,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_3459])).

tff(c_3506,plain,(
    ! [C_2420,A_2421,B_2422] :
      ( k1_funct_1(C_2420,A_2421) = B_2422
      | ~ r2_hidden(k4_tarski(A_2421,B_2422),C_2420)
      | ~ v1_funct_1(C_2420)
      | ~ v1_relat_1(C_2420) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3509,plain,(
    ! [D_2409] :
      ( k1_funct_1('#skF_6',D_2409) = D_2409
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_2409,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3465,c_3506])).

tff(c_3519,plain,(
    ! [D_2423] :
      ( k1_funct_1('#skF_6',D_2423) = D_2423
      | ~ r2_hidden(D_2423,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3509])).

tff(c_3522,plain,(
    k1_funct_1('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3432,c_3519])).

tff(c_3526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3483,c_3522])).

tff(c_3528,plain,(
    k1_relat_1('#skF_6') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3527,plain,(
    k6_relat_1('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_20,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3532,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3527,c_20])).

tff(c_3545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3528,c_3532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.95  
% 4.64/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.95  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.64/1.95  
% 4.64/1.95  %Foreground sorts:
% 4.64/1.95  
% 4.64/1.95  
% 4.64/1.95  %Background operators:
% 4.64/1.95  
% 4.64/1.95  
% 4.64/1.95  %Foreground operators:
% 4.64/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.64/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.64/1.95  tff('#skF_7', type, '#skF_7': $i).
% 4.64/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.64/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.64/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.64/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.64/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.64/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.64/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.64/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.64/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.64/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.64/1.95  
% 4.64/1.97  tff(f_68, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 4.64/1.97  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 4.64/1.97  tff(f_54, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.64/1.97  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.64/1.97  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.64/1.97  tff(c_50, plain, (k6_relat_1('#skF_5')='#skF_6' | k1_relat_1('#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.64/1.97  tff(c_81, plain, (k1_relat_1('#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_50])).
% 4.64/1.97  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_5') | k1_relat_1('#skF_6')!='#skF_5' | k6_relat_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.64/1.97  tff(c_88, plain, (r2_hidden('#skF_7', '#skF_5') | k6_relat_1('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_42])).
% 4.64/1.97  tff(c_89, plain, (k6_relat_1('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_88])).
% 4.64/1.97  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.64/1.97  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.64/1.97  tff(c_166, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), A_40) | r2_hidden(k4_tarski('#skF_3'(A_40, B_41), '#skF_4'(A_40, B_41)), B_41) | k6_relat_1(A_40)=B_41 | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_32, plain, (![A_11, C_13, B_12]: (r2_hidden(A_11, k1_relat_1(C_13)) | ~r2_hidden(k4_tarski(A_11, B_12), C_13) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.64/1.97  tff(c_202, plain, (![A_44, B_45]: (r2_hidden('#skF_3'(A_44, B_45), k1_relat_1(B_45)) | ~v1_funct_1(B_45) | r2_hidden('#skF_1'(A_44, B_45), A_44) | k6_relat_1(A_44)=B_45 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_166, c_32])).
% 4.64/1.97  tff(c_207, plain, (![A_44]: (r2_hidden('#skF_3'(A_44, '#skF_6'), '#skF_5') | ~v1_funct_1('#skF_6') | r2_hidden('#skF_1'(A_44, '#skF_6'), A_44) | k6_relat_1(A_44)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_202])).
% 4.64/1.97  tff(c_212, plain, (![A_44]: (r2_hidden('#skF_3'(A_44, '#skF_6'), '#skF_5') | r2_hidden('#skF_1'(A_44, '#skF_6'), A_44) | k6_relat_1(A_44)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_207])).
% 4.64/1.97  tff(c_1243, plain, (![A_863, B_864]: (r2_hidden('#skF_1'(A_863, B_864), A_863) | '#skF_3'(A_863, B_864)!='#skF_4'(A_863, B_864) | ~r2_hidden('#skF_3'(A_863, B_864), A_863) | k6_relat_1(A_863)=B_864 | ~v1_relat_1(B_864))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_1265, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | ~v1_relat_1('#skF_6') | r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_212, c_1243])).
% 4.64/1.97  tff(c_1291, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1265])).
% 4.64/1.97  tff(c_1292, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_89, c_1291])).
% 4.64/1.97  tff(c_1298, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1292])).
% 4.64/1.97  tff(c_215, plain, (![A_46]: (r2_hidden('#skF_3'(A_46, '#skF_6'), '#skF_5') | r2_hidden('#skF_1'(A_46, '#skF_6'), A_46) | k6_relat_1(A_46)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_207])).
% 4.64/1.97  tff(c_44, plain, (![C_16]: (k6_relat_1('#skF_5')='#skF_6' | k1_funct_1('#skF_6', C_16)=C_16 | ~r2_hidden(C_16, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.64/1.97  tff(c_101, plain, (![C_16]: (k1_funct_1('#skF_6', C_16)=C_16 | ~r2_hidden(C_16, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_89, c_44])).
% 4.64/1.97  tff(c_250, plain, (![A_49]: (k1_funct_1('#skF_6', '#skF_3'(A_49, '#skF_6'))='#skF_3'(A_49, '#skF_6') | r2_hidden('#skF_1'(A_49, '#skF_6'), A_49) | k6_relat_1(A_49)='#skF_6')), inference(resolution, [status(thm)], [c_215, c_101])).
% 4.64/1.97  tff(c_254, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_250, c_101])).
% 4.64/1.97  tff(c_257, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_89, c_254])).
% 4.64/1.97  tff(c_258, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_257])).
% 4.64/1.97  tff(c_30, plain, (![C_13, A_11, B_12]: (k1_funct_1(C_13, A_11)=B_12 | ~r2_hidden(k4_tarski(A_11, B_12), C_13) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.64/1.97  tff(c_186, plain, (![B_41, A_40]: (k1_funct_1(B_41, '#skF_3'(A_40, B_41))='#skF_4'(A_40, B_41) | ~v1_funct_1(B_41) | r2_hidden('#skF_1'(A_40, B_41), A_40) | k6_relat_1(A_40)=B_41 | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_166, c_30])).
% 4.64/1.97  tff(c_222, plain, (![A_47, B_48]: ('#skF_2'(A_47, B_48)='#skF_1'(A_47, B_48) | r2_hidden(k4_tarski('#skF_3'(A_47, B_48), '#skF_4'(A_47, B_48)), B_48) | k6_relat_1(A_47)=B_48 | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_1358, plain, (![B_870, A_871]: (k1_funct_1(B_870, '#skF_3'(A_871, B_870))='#skF_4'(A_871, B_870) | ~v1_funct_1(B_870) | '#skF_2'(A_871, B_870)='#skF_1'(A_871, B_870) | k6_relat_1(A_871)=B_870 | ~v1_relat_1(B_870))), inference(resolution, [status(thm)], [c_222, c_30])).
% 4.64/1.97  tff(c_1371, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_4'('#skF_5', '#skF_6') | ~v1_funct_1('#skF_6') | '#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1358, c_258])).
% 4.64/1.97  tff(c_1403, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_4'('#skF_5', '#skF_6') | '#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1371])).
% 4.64/1.97  tff(c_1404, plain, ('#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_89, c_1298, c_1403])).
% 4.64/1.97  tff(c_1847, plain, (![A_1600, B_1601]: (~r2_hidden(k4_tarski('#skF_1'(A_1600, B_1601), '#skF_2'(A_1600, B_1601)), B_1601) | r2_hidden(k4_tarski('#skF_3'(A_1600, B_1601), '#skF_4'(A_1600, B_1601)), B_1601) | k6_relat_1(A_1600)=B_1601 | ~v1_relat_1(B_1601))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_2065, plain, (![B_1630, A_1631]: (k1_funct_1(B_1630, '#skF_3'(A_1631, B_1630))='#skF_4'(A_1631, B_1630) | ~v1_funct_1(B_1630) | ~r2_hidden(k4_tarski('#skF_1'(A_1631, B_1630), '#skF_2'(A_1631, B_1630)), B_1630) | k6_relat_1(A_1631)=B_1630 | ~v1_relat_1(B_1630))), inference(resolution, [status(thm)], [c_1847, c_30])).
% 4.64/1.97  tff(c_2068, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | ~v1_funct_1('#skF_6') | ~r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1404, c_2065])).
% 4.64/1.97  tff(c_2070, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_4'('#skF_5', '#skF_6') | ~r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_258, c_2068])).
% 4.64/1.97  tff(c_2071, plain, (~r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_89, c_1298, c_2070])).
% 4.64/1.97  tff(c_1319, plain, (![B_868, A_869]: (k1_funct_1(B_868, '#skF_3'(A_869, B_868))='#skF_4'(A_869, B_868) | ~v1_funct_1(B_868) | r2_hidden('#skF_1'(A_869, B_868), A_869) | k6_relat_1(A_869)=B_868 | ~v1_relat_1(B_868))), inference(resolution, [status(thm)], [c_166, c_30])).
% 4.64/1.97  tff(c_2095, plain, (![B_1634]: (k1_funct_1('#skF_6', '#skF_1'('#skF_5', B_1634))='#skF_1'('#skF_5', B_1634) | k1_funct_1(B_1634, '#skF_3'('#skF_5', B_1634))='#skF_4'('#skF_5', B_1634) | ~v1_funct_1(B_1634) | k6_relat_1('#skF_5')=B_1634 | ~v1_relat_1(B_1634))), inference(resolution, [status(thm)], [c_1319, c_101])).
% 4.64/1.97  tff(c_2118, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_4'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | ~v1_funct_1('#skF_6') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2095, c_258])).
% 4.64/1.97  tff(c_2170, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_4'('#skF_5', '#skF_6') | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2118])).
% 4.64/1.97  tff(c_2171, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_89, c_1298, c_2170])).
% 4.64/1.97  tff(c_28, plain, (![A_11, C_13]: (r2_hidden(k4_tarski(A_11, k1_funct_1(C_13, A_11)), C_13) | ~r2_hidden(A_11, k1_relat_1(C_13)) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.64/1.97  tff(c_2195, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2171, c_28])).
% 4.64/1.97  tff(c_2200, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_81, c_2195])).
% 4.64/1.97  tff(c_2201, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2071, c_2200])).
% 4.64/1.97  tff(c_2205, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_4'('#skF_5', '#skF_6') | ~v1_funct_1('#skF_6') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_186, c_2201])).
% 4.64/1.97  tff(c_2213, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_4'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_258, c_2205])).
% 4.64/1.97  tff(c_2215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_1298, c_2213])).
% 4.64/1.97  tff(c_2217, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_4'('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1292])).
% 4.64/1.97  tff(c_262, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6'), '#skF_3'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_258, c_28])).
% 4.64/1.97  tff(c_266, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6'), '#skF_3'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_81, c_262])).
% 4.64/1.97  tff(c_269, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_266])).
% 4.64/1.97  tff(c_272, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_212, c_269])).
% 4.64/1.97  tff(c_275, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_89, c_272])).
% 4.64/1.97  tff(c_279, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_275, c_101])).
% 4.64/1.97  tff(c_283, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_279, c_28])).
% 4.64/1.97  tff(c_287, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_275, c_81, c_283])).
% 4.64/1.97  tff(c_350, plain, (![A_57, B_58]: (r2_hidden('#skF_3'(A_57, B_58), k1_relat_1(B_58)) | ~v1_funct_1(B_58) | '#skF_2'(A_57, B_58)='#skF_1'(A_57, B_58) | k6_relat_1(A_57)=B_58 | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_222, c_32])).
% 4.64/1.97  tff(c_357, plain, (![A_57]: (r2_hidden('#skF_3'(A_57, '#skF_6'), '#skF_5') | ~v1_funct_1('#skF_6') | '#skF_2'(A_57, '#skF_6')='#skF_1'(A_57, '#skF_6') | k6_relat_1(A_57)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_350])).
% 4.64/1.97  tff(c_366, plain, (![A_59]: (r2_hidden('#skF_3'(A_59, '#skF_6'), '#skF_5') | '#skF_2'(A_59, '#skF_6')='#skF_1'(A_59, '#skF_6') | k6_relat_1(A_59)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_357])).
% 4.64/1.97  tff(c_373, plain, ('#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_366, c_269])).
% 4.64/1.97  tff(c_383, plain, ('#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_89, c_373])).
% 4.64/1.97  tff(c_932, plain, (![A_809, B_810]: (~r2_hidden(k4_tarski('#skF_1'(A_809, B_810), '#skF_2'(A_809, B_810)), B_810) | r2_hidden(k4_tarski('#skF_3'(A_809, B_810), '#skF_4'(A_809, B_810)), B_810) | k6_relat_1(A_809)=B_810 | ~v1_relat_1(B_810))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_1122, plain, (![A_850, B_851]: (r2_hidden('#skF_3'(A_850, B_851), k1_relat_1(B_851)) | ~v1_funct_1(B_851) | ~r2_hidden(k4_tarski('#skF_1'(A_850, B_851), '#skF_2'(A_850, B_851)), B_851) | k6_relat_1(A_850)=B_851 | ~v1_relat_1(B_851))), inference(resolution, [status(thm)], [c_932, c_32])).
% 4.64/1.97  tff(c_1125, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_383, c_1122])).
% 4.64/1.97  tff(c_1127, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_287, c_34, c_81, c_1125])).
% 4.64/1.97  tff(c_1129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_269, c_1127])).
% 4.64/1.97  tff(c_1131, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_266])).
% 4.64/1.97  tff(c_2223, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2217, c_1131])).
% 4.64/1.97  tff(c_2216, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_1292])).
% 4.64/1.97  tff(c_2221, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2216, c_101])).
% 4.64/1.97  tff(c_2339, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2221, c_28])).
% 4.64/1.97  tff(c_2343, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2216, c_81, c_2339])).
% 4.64/1.97  tff(c_1168, plain, (![A_857, B_858]: (r2_hidden('#skF_3'(A_857, B_858), k1_relat_1(B_858)) | ~v1_funct_1(B_858) | '#skF_2'(A_857, B_858)='#skF_1'(A_857, B_858) | k6_relat_1(A_857)=B_858 | ~v1_relat_1(B_858))), inference(resolution, [status(thm)], [c_222, c_32])).
% 4.64/1.97  tff(c_1171, plain, (![A_857]: (r2_hidden('#skF_3'(A_857, '#skF_6'), '#skF_5') | ~v1_funct_1('#skF_6') | '#skF_2'(A_857, '#skF_6')='#skF_1'(A_857, '#skF_6') | k6_relat_1(A_857)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_1168])).
% 4.64/1.97  tff(c_1176, plain, (![A_857]: (r2_hidden('#skF_3'(A_857, '#skF_6'), '#skF_5') | '#skF_2'(A_857, '#skF_6')='#skF_1'(A_857, '#skF_6') | k6_relat_1(A_857)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1171])).
% 4.64/1.97  tff(c_2277, plain, (![A_1635, B_1636]: ('#skF_2'(A_1635, B_1636)='#skF_1'(A_1635, B_1636) | '#skF_3'(A_1635, B_1636)!='#skF_4'(A_1635, B_1636) | ~r2_hidden('#skF_3'(A_1635, B_1636), A_1635) | k6_relat_1(A_1635)=B_1636 | ~v1_relat_1(B_1636))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_2287, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | ~v1_relat_1('#skF_6') | '#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1176, c_2277])).
% 4.64/1.97  tff(c_2315, plain, ('#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2217, c_2287])).
% 4.64/1.97  tff(c_2316, plain, ('#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_89, c_2315])).
% 4.64/1.97  tff(c_2539, plain, (![A_1646, B_1647]: (~r2_hidden(k4_tarski('#skF_1'(A_1646, B_1647), '#skF_2'(A_1646, B_1647)), B_1647) | '#skF_3'(A_1646, B_1647)!='#skF_4'(A_1646, B_1647) | ~r2_hidden('#skF_3'(A_1646, B_1647), A_1646) | k6_relat_1(A_1646)=B_1647 | ~v1_relat_1(B_1647))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_2542, plain, (~r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | '#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2316, c_2539])).
% 4.64/1.97  tff(c_2544, plain, (k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2223, c_2217, c_2217, c_2343, c_2542])).
% 4.64/1.97  tff(c_2546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_2544])).
% 4.64/1.97  tff(c_2548, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))!='#skF_3'('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_257])).
% 4.64/1.97  tff(c_221, plain, (![A_46]: (k1_funct_1('#skF_6', '#skF_3'(A_46, '#skF_6'))='#skF_3'(A_46, '#skF_6') | r2_hidden('#skF_1'(A_46, '#skF_6'), A_46) | k6_relat_1(A_46)='#skF_6')), inference(resolution, [status(thm)], [c_215, c_101])).
% 4.64/1.97  tff(c_2547, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_6'))='#skF_1'('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_257])).
% 4.64/1.97  tff(c_2552, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2547, c_28])).
% 4.64/1.97  tff(c_2556, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_81, c_2552])).
% 4.64/1.97  tff(c_2558, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2556])).
% 4.64/1.97  tff(c_2562, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_221, c_2558])).
% 4.64/1.97  tff(c_2568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_2548, c_2562])).
% 4.64/1.97  tff(c_2569, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6')), inference(splitRight, [status(thm)], [c_2556])).
% 4.64/1.97  tff(c_2630, plain, (![A_1654, B_1655]: (r2_hidden('#skF_3'(A_1654, B_1655), k1_relat_1(B_1655)) | ~v1_funct_1(B_1655) | '#skF_2'(A_1654, B_1655)='#skF_1'(A_1654, B_1655) | k6_relat_1(A_1654)=B_1655 | ~v1_relat_1(B_1655))), inference(resolution, [status(thm)], [c_222, c_32])).
% 4.64/1.97  tff(c_2637, plain, (![A_1654]: (r2_hidden('#skF_3'(A_1654, '#skF_6'), '#skF_5') | ~v1_funct_1('#skF_6') | '#skF_2'(A_1654, '#skF_6')='#skF_1'(A_1654, '#skF_6') | k6_relat_1(A_1654)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_2630])).
% 4.64/1.97  tff(c_2646, plain, (![A_1656]: (r2_hidden('#skF_3'(A_1656, '#skF_6'), '#skF_5') | '#skF_2'(A_1656, '#skF_6')='#skF_1'(A_1656, '#skF_6') | k6_relat_1(A_1656)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2637])).
% 4.64/1.97  tff(c_2659, plain, (![A_1657]: (k1_funct_1('#skF_6', '#skF_3'(A_1657, '#skF_6'))='#skF_3'(A_1657, '#skF_6') | '#skF_2'(A_1657, '#skF_6')='#skF_1'(A_1657, '#skF_6') | k6_relat_1(A_1657)='#skF_6')), inference(resolution, [status(thm)], [c_2646, c_101])).
% 4.64/1.97  tff(c_2665, plain, ('#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6') | k6_relat_1('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2659, c_2548])).
% 4.64/1.97  tff(c_2675, plain, ('#skF_2'('#skF_5', '#skF_6')='#skF_1'('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_89, c_2665])).
% 4.64/1.97  tff(c_3366, plain, (![A_2402, B_2403]: (~r2_hidden(k4_tarski('#skF_1'(A_2402, B_2403), '#skF_2'(A_2402, B_2403)), B_2403) | '#skF_3'(A_2402, B_2403)!='#skF_4'(A_2402, B_2403) | ~r2_hidden('#skF_3'(A_2402, B_2403), A_2402) | k6_relat_1(A_2402)=B_2403 | ~v1_relat_1(B_2403))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_3369, plain, (~r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | '#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2675, c_3366])).
% 4.64/1.97  tff(c_3371, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2569, c_3369])).
% 4.64/1.97  tff(c_3372, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_4'('#skF_5', '#skF_6') | ~r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_89, c_3371])).
% 4.64/1.97  tff(c_3373, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3372])).
% 4.64/1.97  tff(c_3195, plain, (![A_2364, B_2365]: (~r2_hidden(k4_tarski('#skF_1'(A_2364, B_2365), '#skF_2'(A_2364, B_2365)), B_2365) | r2_hidden(k4_tarski('#skF_3'(A_2364, B_2365), '#skF_4'(A_2364, B_2365)), B_2365) | k6_relat_1(A_2364)=B_2365 | ~v1_relat_1(B_2365))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_3398, plain, (![A_2405, B_2406]: (r2_hidden('#skF_3'(A_2405, B_2406), k1_relat_1(B_2406)) | ~v1_funct_1(B_2406) | ~r2_hidden(k4_tarski('#skF_1'(A_2405, B_2406), '#skF_2'(A_2405, B_2406)), B_2406) | k6_relat_1(A_2405)=B_2406 | ~v1_relat_1(B_2406))), inference(resolution, [status(thm)], [c_3195, c_32])).
% 4.64/1.97  tff(c_3401, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_1'('#skF_5', '#skF_6')), '#skF_6') | k6_relat_1('#skF_5')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2675, c_3398])).
% 4.64/1.97  tff(c_3403, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | k6_relat_1('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2569, c_34, c_81, c_3401])).
% 4.64/1.97  tff(c_3405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_3373, c_3403])).
% 4.64/1.97  tff(c_3407, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_3372])).
% 4.64/1.97  tff(c_3416, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_6'))='#skF_3'('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_3407, c_101])).
% 4.64/1.97  tff(c_3431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2548, c_3416])).
% 4.64/1.97  tff(c_3433, plain, (k6_relat_1('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_88])).
% 4.64/1.97  tff(c_40, plain, (k1_funct_1('#skF_6', '#skF_7')!='#skF_7' | k1_relat_1('#skF_6')!='#skF_5' | k6_relat_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.64/1.97  tff(c_3483, plain, (k1_funct_1('#skF_6', '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3433, c_81, c_40])).
% 4.64/1.97  tff(c_3432, plain, (r2_hidden('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 4.64/1.97  tff(c_24, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.64/1.97  tff(c_14, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.97  tff(c_3459, plain, (![D_2409, A_2410]: (r2_hidden(k4_tarski(D_2409, D_2409), k6_relat_1(A_2410)) | ~r2_hidden(D_2409, A_2410))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14])).
% 4.64/1.97  tff(c_3465, plain, (![D_2409]: (r2_hidden(k4_tarski(D_2409, D_2409), '#skF_6') | ~r2_hidden(D_2409, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3433, c_3459])).
% 4.64/1.97  tff(c_3506, plain, (![C_2420, A_2421, B_2422]: (k1_funct_1(C_2420, A_2421)=B_2422 | ~r2_hidden(k4_tarski(A_2421, B_2422), C_2420) | ~v1_funct_1(C_2420) | ~v1_relat_1(C_2420))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.64/1.97  tff(c_3509, plain, (![D_2409]: (k1_funct_1('#skF_6', D_2409)=D_2409 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(D_2409, '#skF_5'))), inference(resolution, [status(thm)], [c_3465, c_3506])).
% 4.64/1.97  tff(c_3519, plain, (![D_2423]: (k1_funct_1('#skF_6', D_2423)=D_2423 | ~r2_hidden(D_2423, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3509])).
% 4.64/1.97  tff(c_3522, plain, (k1_funct_1('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_3432, c_3519])).
% 4.64/1.97  tff(c_3526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3483, c_3522])).
% 4.64/1.97  tff(c_3528, plain, (k1_relat_1('#skF_6')!='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 4.64/1.97  tff(c_3527, plain, (k6_relat_1('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 4.64/1.97  tff(c_20, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.64/1.97  tff(c_3532, plain, (k1_relat_1('#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3527, c_20])).
% 4.64/1.97  tff(c_3545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3528, c_3532])).
% 4.64/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.97  
% 4.64/1.97  Inference rules
% 4.64/1.97  ----------------------
% 4.64/1.97  #Ref     : 0
% 4.64/1.97  #Sup     : 637
% 4.64/1.97  #Fact    : 0
% 4.64/1.97  #Define  : 0
% 4.64/1.97  #Split   : 13
% 4.64/1.97  #Chain   : 0
% 4.64/1.97  #Close   : 0
% 4.64/1.97  
% 4.64/1.97  Ordering : KBO
% 4.64/1.97  
% 4.64/1.97  Simplification rules
% 4.64/1.97  ----------------------
% 4.64/1.97  #Subsume      : 126
% 4.64/1.97  #Demod        : 638
% 4.64/1.97  #Tautology    : 263
% 4.64/1.97  #SimpNegUnit  : 74
% 4.64/1.97  #BackRed      : 3
% 4.64/1.97  
% 4.64/1.97  #Partial instantiations: 1314
% 4.64/1.97  #Strategies tried      : 1
% 4.64/1.97  
% 4.64/1.97  Timing (in seconds)
% 4.64/1.97  ----------------------
% 4.64/1.98  Preprocessing        : 0.32
% 4.64/1.98  Parsing              : 0.16
% 4.64/1.98  CNF conversion       : 0.02
% 4.64/1.98  Main loop            : 0.78
% 4.64/1.98  Inferencing          : 0.33
% 4.64/1.98  Reduction            : 0.24
% 4.64/1.98  Demodulation         : 0.16
% 4.64/1.98  BG Simplification    : 0.04
% 4.64/1.98  Subsumption          : 0.12
% 4.64/1.98  Abstraction          : 0.06
% 4.64/1.98  MUC search           : 0.00
% 4.64/1.98  Cooper               : 0.00
% 4.64/1.98  Total                : 1.15
% 4.64/1.98  Index Insertion      : 0.00
% 4.64/1.98  Index Deletion       : 0.00
% 4.64/1.98  Index Matching       : 0.00
% 4.64/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
