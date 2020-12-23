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
% DateTime   : Thu Dec  3 10:03:08 EST 2020

% Result     : Theorem 12.37s
% Output     : CNFRefutation 12.56s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 629 expanded)
%              Number of leaves         :   26 ( 234 expanded)
%              Depth                    :   16
%              Number of atoms          :  274 (1836 expanded)
%              Number of equality atoms :   91 ( 709 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_42,plain,(
    ! [A_49,B_50] : v1_relat_1('#skF_6'(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    ! [A_49,B_50] : v1_funct_1('#skF_6'(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_49,B_50] : k1_relat_1('#skF_6'(A_49,B_50)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30116,plain,(
    ! [A_5982,C_5983] :
      ( r2_hidden('#skF_5'(A_5982,k2_relat_1(A_5982),C_5983),k1_relat_1(A_5982))
      | ~ r2_hidden(C_5983,k2_relat_1(A_5982))
      | ~ v1_funct_1(A_5982)
      | ~ v1_relat_1(A_5982) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30124,plain,(
    ! [A_49,B_50,C_5983] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_5983),A_49)
      | ~ r2_hidden(C_5983,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_30116])).

tff(c_30744,plain,(
    ! [A_6070,B_6071,C_6072] :
      ( r2_hidden('#skF_5'('#skF_6'(A_6070,B_6071),k2_relat_1('#skF_6'(A_6070,B_6071)),C_6072),A_6070)
      | ~ r2_hidden(C_6072,k2_relat_1('#skF_6'(A_6070,B_6071))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30124])).

tff(c_64,plain,(
    ! [A_69] :
      ( k2_relat_1(A_69) = k1_xboole_0
      | k1_relat_1(A_69) != k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [A_49,B_50] :
      ( k2_relat_1('#skF_6'(A_49,B_50)) = k1_xboole_0
      | k1_relat_1('#skF_6'(A_49,B_50)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_70,plain,(
    ! [B_50] : k2_relat_1('#skF_6'(k1_xboole_0,B_50)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_67])).

tff(c_69,plain,(
    ! [A_49,B_50] :
      ( k2_relat_1('#skF_6'(A_49,B_50)) = k1_xboole_0
      | k1_xboole_0 != A_49 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_67])).

tff(c_30102,plain,(
    ! [B_5980,A_5981] :
      ( r2_hidden(k1_funct_1(B_5980,A_5981),k2_relat_1(B_5980))
      | ~ r2_hidden(A_5981,k1_relat_1(B_5980))
      | ~ v1_funct_1(B_5980)
      | ~ v1_relat_1(B_5980) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30110,plain,(
    ! [A_49,B_50,A_5981] :
      ( r2_hidden(k1_funct_1('#skF_6'(A_49,B_50),A_5981),k1_xboole_0)
      | ~ r2_hidden(A_5981,k1_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_30102])).

tff(c_30327,plain,(
    ! [A_6023,B_6024,A_6025] :
      ( r2_hidden(k1_funct_1('#skF_6'(A_6023,B_6024),A_6025),k1_xboole_0)
      | ~ r2_hidden(A_6025,A_6023)
      | k1_xboole_0 != A_6023 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30110])).

tff(c_36,plain,(
    ! [A_49,B_50,D_55] :
      ( k1_funct_1('#skF_6'(A_49,B_50),D_55) = B_50
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30107,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,k1_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_30102])).

tff(c_30113,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30107])).

tff(c_30329,plain,(
    ! [B_50,A_6025,A_6023] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(k1_xboole_0,B_50)))
      | ~ r2_hidden(A_6025,A_6023)
      | k1_xboole_0 != A_6023 ) ),
    inference(resolution,[status(thm)],[c_30327,c_30113])).

tff(c_30340,plain,(
    ! [B_50,A_6025,A_6023] :
      ( r2_hidden(B_50,k1_xboole_0)
      | ~ r2_hidden(A_6025,A_6023)
      | k1_xboole_0 != A_6023 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_30329])).

tff(c_30346,plain,(
    ! [A_6025,A_6023] :
      ( ~ r2_hidden(A_6025,A_6023)
      | k1_xboole_0 != A_6023 ) ),
    inference(splitLeft,[status(thm)],[c_30340])).

tff(c_30775,plain,(
    ! [A_6073,C_6074,B_6075] :
      ( k1_xboole_0 != A_6073
      | ~ r2_hidden(C_6074,k2_relat_1('#skF_6'(A_6073,B_6075))) ) ),
    inference(resolution,[status(thm)],[c_30744,c_30346])).

tff(c_30828,plain,(
    ! [A_6076,B_6077,B_6078] :
      ( k1_xboole_0 != A_6076
      | r1_tarski(k2_relat_1('#skF_6'(A_6076,B_6077)),B_6078) ) ),
    inference(resolution,[status(thm)],[c_6,c_30775])).

tff(c_30130,plain,(
    ! [B_5984,A_5985,D_5986] :
      ( r2_hidden(B_5984,k2_relat_1('#skF_6'(A_5985,B_5984)))
      | ~ r2_hidden(D_5986,A_5985) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30107])).

tff(c_30143,plain,(
    ! [B_5987,A_5988,B_5989] :
      ( r2_hidden(B_5987,k2_relat_1('#skF_6'(A_5988,B_5987)))
      | r1_tarski(A_5988,B_5989) ) ),
    inference(resolution,[status(thm)],[c_6,c_30130])).

tff(c_30154,plain,(
    ! [B_50,A_49,B_5989] :
      ( r2_hidden(B_50,k1_xboole_0)
      | r1_tarski(A_49,B_5989)
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_30143])).

tff(c_30190,plain,(
    ! [A_5992,B_5993] :
      ( r1_tarski(A_5992,B_5993)
      | k1_xboole_0 != A_5992 ) ),
    inference(splitLeft,[status(thm)],[c_30154])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30200,plain,(
    ! [B_5993,A_5992] :
      ( B_5993 = A_5992
      | ~ r1_tarski(B_5993,A_5992)
      | k1_xboole_0 != A_5992 ) ),
    inference(resolution,[status(thm)],[c_30190,c_8])).

tff(c_30867,plain,(
    ! [B_6077] : k2_relat_1('#skF_6'(k1_xboole_0,B_6077)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30828,c_30200])).

tff(c_30262,plain,(
    ! [A_6011,B_6012] :
      ( r2_hidden('#skF_3'(A_6011,B_6012),k1_relat_1(A_6011))
      | r2_hidden('#skF_4'(A_6011,B_6012),B_6012)
      | k2_relat_1(A_6011) = B_6012
      | ~ v1_funct_1(A_6011)
      | ~ v1_relat_1(A_6011) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30273,plain,(
    ! [A_49,B_50,B_6012] :
      ( r2_hidden('#skF_3'('#skF_6'(A_49,B_50),B_6012),A_49)
      | r2_hidden('#skF_4'('#skF_6'(A_49,B_50),B_6012),B_6012)
      | k2_relat_1('#skF_6'(A_49,B_50)) = B_6012
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_30262])).

tff(c_31416,plain,(
    ! [A_6133,B_6134,B_6135] :
      ( r2_hidden('#skF_3'('#skF_6'(A_6133,B_6134),B_6135),A_6133)
      | r2_hidden('#skF_4'('#skF_6'(A_6133,B_6134),B_6135),B_6135)
      | k2_relat_1('#skF_6'(A_6133,B_6134)) = B_6135 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30273])).

tff(c_22,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_5'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30385,plain,(
    ! [A_6028,A_6029] :
      ( ~ r2_hidden(A_6028,A_6029)
      | k1_xboole_0 != A_6029 ) ),
    inference(splitLeft,[status(thm)],[c_30340])).

tff(c_30492,plain,(
    ! [A_6047,C_6048] :
      ( k1_relat_1(A_6047) != k1_xboole_0
      | ~ r2_hidden(C_6048,k2_relat_1(A_6047))
      | ~ v1_funct_1(A_6047)
      | ~ v1_relat_1(A_6047) ) ),
    inference(resolution,[status(thm)],[c_22,c_30385])).

tff(c_30523,plain,(
    ! [A_49,B_50,C_6048] :
      ( k1_relat_1('#skF_6'(A_49,B_50)) != k1_xboole_0
      | ~ r2_hidden(C_6048,k1_xboole_0)
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_30492])).

tff(c_30539,plain,(
    ! [C_6048,A_49] :
      ( ~ r2_hidden(C_6048,k1_xboole_0)
      | k1_xboole_0 != A_49 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30523])).

tff(c_30549,plain,(
    ! [A_49] : k1_xboole_0 != A_49 ),
    inference(splitLeft,[status(thm)],[c_30539])).

tff(c_30561,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_30549])).

tff(c_30562,plain,(
    ! [C_6048] : ~ r2_hidden(C_6048,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_30539])).

tff(c_31431,plain,(
    ! [B_6134,B_6135] :
      ( r2_hidden('#skF_4'('#skF_6'(k1_xboole_0,B_6134),B_6135),B_6135)
      | k2_relat_1('#skF_6'(k1_xboole_0,B_6134)) = B_6135 ) ),
    inference(resolution,[status(thm)],[c_31416,c_30562])).

tff(c_31479,plain,(
    ! [B_6134,B_6135] :
      ( r2_hidden('#skF_4'('#skF_6'(k1_xboole_0,B_6134),B_6135),B_6135)
      | k1_xboole_0 = B_6135 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30867,c_31431])).

tff(c_30129,plain,(
    ! [A_49,B_50,C_5983] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_5983),A_49)
      | ~ r2_hidden(C_5983,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30124])).

tff(c_30159,plain,(
    ! [A_5990,C_5991] :
      ( k1_funct_1(A_5990,'#skF_5'(A_5990,k2_relat_1(A_5990),C_5991)) = C_5991
      | ~ r2_hidden(C_5991,k2_relat_1(A_5990))
      | ~ v1_funct_1(A_5990)
      | ~ v1_relat_1(A_5990) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30176,plain,(
    ! [C_5991,B_50,A_49] :
      ( C_5991 = B_50
      | ~ r2_hidden(C_5991,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_5991),A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_30159])).

tff(c_32228,plain,(
    ! [C_6159,B_6160,A_6161] :
      ( C_6159 = B_6160
      | ~ r2_hidden(C_6159,k2_relat_1('#skF_6'(A_6161,B_6160)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_6161,B_6160),k2_relat_1('#skF_6'(A_6161,B_6160)),C_6159),A_6161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30176])).

tff(c_32242,plain,(
    ! [C_6162,B_6163,A_6164] :
      ( C_6162 = B_6163
      | ~ r2_hidden(C_6162,k2_relat_1('#skF_6'(A_6164,B_6163))) ) ),
    inference(resolution,[status(thm)],[c_30129,c_32228])).

tff(c_39252,plain,(
    ! [A_8604,B_8605,B_8606] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_8604,B_8605)),B_8606) = B_8605
      | r1_tarski(k2_relat_1('#skF_6'(A_8604,B_8605)),B_8606) ) ),
    inference(resolution,[status(thm)],[c_6,c_32242])).

tff(c_46,plain,(
    ! [C_59] :
      ( ~ r1_tarski(k2_relat_1(C_59),'#skF_7')
      | k1_relat_1(C_59) != '#skF_8'
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_39362,plain,(
    ! [A_8604,B_8605] :
      ( k1_relat_1('#skF_6'(A_8604,B_8605)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_8604,B_8605))
      | ~ v1_relat_1('#skF_6'(A_8604,B_8605))
      | '#skF_1'(k2_relat_1('#skF_6'(A_8604,B_8605)),'#skF_7') = B_8605 ) ),
    inference(resolution,[status(thm)],[c_39252,c_46])).

tff(c_39479,plain,(
    ! [A_8624,B_8625] :
      ( A_8624 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(A_8624,B_8625)),'#skF_7') = B_8625 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_39362])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39632,plain,(
    ! [B_8662,A_8663] :
      ( ~ r2_hidden(B_8662,'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(A_8663,B_8662)),'#skF_7')
      | A_8663 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39479,c_4])).

tff(c_39665,plain,(
    ! [A_8663,B_8662] :
      ( k1_relat_1('#skF_6'(A_8663,B_8662)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_8663,B_8662))
      | ~ v1_relat_1('#skF_6'(A_8663,B_8662))
      | ~ r2_hidden(B_8662,'#skF_7')
      | A_8663 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_39632,c_46])).

tff(c_39736,plain,(
    ! [B_8662,A_8663] :
      ( ~ r2_hidden(B_8662,'#skF_7')
      | A_8663 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_39665])).

tff(c_39744,plain,(
    ! [A_8663] : A_8663 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_39736])).

tff(c_39748,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_39744])).

tff(c_39750,plain,(
    ! [B_8681] : ~ r2_hidden(B_8681,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_39736])).

tff(c_39774,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_31479,c_39750])).

tff(c_39810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_39774])).

tff(c_39813,plain,(
    ! [B_8699] : r2_hidden(B_8699,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_30340])).

tff(c_39833,plain,(
    ! [A_1] : r1_tarski(A_1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_39813,c_4])).

tff(c_134,plain,(
    ! [B_89,A_90] :
      ( r2_hidden(k1_funct_1(B_89,A_90),k2_relat_1(B_89))
      | ~ r2_hidden(A_90,k1_relat_1(B_89))
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_139,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,k1_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_134])).

tff(c_148,plain,(
    ! [B_91,A_92,D_93] :
      ( r2_hidden(B_91,k2_relat_1('#skF_6'(A_92,B_91)))
      | ~ r2_hidden(D_93,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_139])).

tff(c_158,plain,(
    ! [B_94,A_95,B_96] :
      ( r2_hidden(B_94,k2_relat_1('#skF_6'(A_95,B_94)))
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_169,plain,(
    ! [B_50,A_49,B_96] :
      ( r2_hidden(B_50,k1_xboole_0)
      | r1_tarski(A_49,B_96)
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_158])).

tff(c_174,plain,(
    ! [B_96] : r1_tarski(k1_xboole_0,B_96) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_80,plain,(
    ! [C_72] :
      ( ~ r1_tarski(k2_relat_1(C_72),'#skF_7')
      | k1_relat_1(C_72) != '#skF_8'
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_83,plain,(
    ! [A_49,B_50] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_7')
      | k1_relat_1('#skF_6'(A_49,B_50)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_80])).

tff(c_85,plain,(
    ! [A_49] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_7')
      | A_49 != '#skF_8'
      | k1_xboole_0 != A_49 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_83])).

tff(c_86,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_86])).

tff(c_178,plain,(
    ! [B_50] : r2_hidden(B_50,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_192,plain,(
    ! [A_98,C_99] :
      ( k1_funct_1(A_98,'#skF_5'(A_98,k2_relat_1(A_98),C_99)) = C_99
      | ~ r2_hidden(C_99,k2_relat_1(A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_209,plain,(
    ! [C_99,B_50,A_49] :
      ( C_99 = B_50
      | ~ r2_hidden(C_99,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_99),A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_192])).

tff(c_17798,plain,(
    ! [C_3303,B_3304,A_3305] :
      ( C_3303 = B_3304
      | ~ r2_hidden(C_3303,k2_relat_1('#skF_6'(A_3305,B_3304)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_3305,B_3304),k2_relat_1('#skF_6'(A_3305,B_3304)),C_3303),A_3305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_209])).

tff(c_17833,plain,(
    ! [C_3303,B_3304] :
      ( C_3303 = B_3304
      | ~ r2_hidden(C_3303,k2_relat_1('#skF_6'(k1_xboole_0,B_3304))) ) ),
    inference(resolution,[status(thm)],[c_178,c_17798])).

tff(c_17842,plain,(
    ! [C_3340,B_3341] : C_3340 = B_3341 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_70,c_17833])).

tff(c_29478,plain,(
    ! [B_3341] : B_3341 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_17842,c_51])).

tff(c_30042,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_29478])).

tff(c_30044,plain,(
    r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_30061,plain,(
    ! [B_5967,A_5968] :
      ( B_5967 = A_5968
      | ~ r1_tarski(B_5967,A_5968)
      | ~ r1_tarski(A_5968,B_5967) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30063,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30044,c_30061])).

tff(c_30068,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_30063])).

tff(c_39865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39833,c_30068])).

tff(c_39867,plain,(
    ! [B_8702] : r2_hidden(B_8702,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_30154])).

tff(c_39879,plain,(
    ! [A_1] : r1_tarski(A_1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_39867,c_4])).

tff(c_39882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39879,c_30068])).

tff(c_39883,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) = k1_xboole_0
      | k1_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39908,plain,(
    ! [A_8710] :
      ( k2_relat_1(A_8710) = '#skF_8'
      | k1_relat_1(A_8710) != '#skF_8'
      | ~ v1_relat_1(A_8710) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39883,c_39883,c_16])).

tff(c_39911,plain,(
    ! [A_49,B_50] :
      ( k2_relat_1('#skF_6'(A_49,B_50)) = '#skF_8'
      | k1_relat_1('#skF_6'(A_49,B_50)) != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_39908])).

tff(c_39913,plain,(
    ! [A_49,B_50] :
      ( k2_relat_1('#skF_6'(A_49,B_50)) = '#skF_8'
      | A_49 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_39911])).

tff(c_39884,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_39890,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39883,c_39884])).

tff(c_39938,plain,(
    ! [C_8716] :
      ( ~ r1_tarski(k2_relat_1(C_8716),'#skF_8')
      | k1_relat_1(C_8716) != '#skF_8'
      | ~ v1_funct_1(C_8716)
      | ~ v1_relat_1(C_8716) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39890,c_46])).

tff(c_39941,plain,(
    ! [A_49,B_50] :
      ( ~ r1_tarski('#skF_8','#skF_8')
      | k1_relat_1('#skF_6'(A_49,B_50)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | A_49 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39913,c_39938])).

tff(c_39943,plain,(
    ! [A_49] : A_49 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_12,c_39941])).

tff(c_39949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39943,c_39890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.37/4.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.37/4.41  
% 12.37/4.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.37/4.42  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 12.37/4.42  
% 12.37/4.42  %Foreground sorts:
% 12.37/4.42  
% 12.37/4.42  
% 12.37/4.42  %Background operators:
% 12.37/4.42  
% 12.37/4.42  
% 12.37/4.42  %Foreground operators:
% 12.37/4.42  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 12.37/4.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.37/4.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.37/4.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.37/4.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.37/4.42  tff('#skF_7', type, '#skF_7': $i).
% 12.37/4.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.37/4.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.37/4.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.37/4.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 12.37/4.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.37/4.42  tff('#skF_8', type, '#skF_8': $i).
% 12.37/4.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.37/4.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.37/4.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.37/4.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.37/4.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.37/4.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.37/4.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.37/4.42  
% 12.56/4.44  tff(f_71, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 12.56/4.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.56/4.44  tff(f_97, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 12.56/4.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.56/4.44  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 12.56/4.44  tff(f_44, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 12.56/4.44  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 12.56/4.44  tff(c_42, plain, (![A_49, B_50]: (v1_relat_1('#skF_6'(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.56/4.44  tff(c_40, plain, (![A_49, B_50]: (v1_funct_1('#skF_6'(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.56/4.44  tff(c_38, plain, (![A_49, B_50]: (k1_relat_1('#skF_6'(A_49, B_50))=A_49)), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.56/4.44  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.56/4.44  tff(c_48, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.56/4.44  tff(c_51, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_48])).
% 12.56/4.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.56/4.44  tff(c_30116, plain, (![A_5982, C_5983]: (r2_hidden('#skF_5'(A_5982, k2_relat_1(A_5982), C_5983), k1_relat_1(A_5982)) | ~r2_hidden(C_5983, k2_relat_1(A_5982)) | ~v1_funct_1(A_5982) | ~v1_relat_1(A_5982))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.56/4.44  tff(c_30124, plain, (![A_49, B_50, C_5983]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_5983), A_49) | ~r2_hidden(C_5983, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_30116])).
% 12.56/4.44  tff(c_30744, plain, (![A_6070, B_6071, C_6072]: (r2_hidden('#skF_5'('#skF_6'(A_6070, B_6071), k2_relat_1('#skF_6'(A_6070, B_6071)), C_6072), A_6070) | ~r2_hidden(C_6072, k2_relat_1('#skF_6'(A_6070, B_6071))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30124])).
% 12.56/4.44  tff(c_64, plain, (![A_69]: (k2_relat_1(A_69)=k1_xboole_0 | k1_relat_1(A_69)!=k1_xboole_0 | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.56/4.44  tff(c_67, plain, (![A_49, B_50]: (k2_relat_1('#skF_6'(A_49, B_50))=k1_xboole_0 | k1_relat_1('#skF_6'(A_49, B_50))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_64])).
% 12.56/4.44  tff(c_70, plain, (![B_50]: (k2_relat_1('#skF_6'(k1_xboole_0, B_50))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_67])).
% 12.56/4.44  tff(c_69, plain, (![A_49, B_50]: (k2_relat_1('#skF_6'(A_49, B_50))=k1_xboole_0 | k1_xboole_0!=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_67])).
% 12.56/4.44  tff(c_30102, plain, (![B_5980, A_5981]: (r2_hidden(k1_funct_1(B_5980, A_5981), k2_relat_1(B_5980)) | ~r2_hidden(A_5981, k1_relat_1(B_5980)) | ~v1_funct_1(B_5980) | ~v1_relat_1(B_5980))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.56/4.44  tff(c_30110, plain, (![A_49, B_50, A_5981]: (r2_hidden(k1_funct_1('#skF_6'(A_49, B_50), A_5981), k1_xboole_0) | ~r2_hidden(A_5981, k1_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_69, c_30102])).
% 12.56/4.44  tff(c_30327, plain, (![A_6023, B_6024, A_6025]: (r2_hidden(k1_funct_1('#skF_6'(A_6023, B_6024), A_6025), k1_xboole_0) | ~r2_hidden(A_6025, A_6023) | k1_xboole_0!=A_6023)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30110])).
% 12.56/4.44  tff(c_36, plain, (![A_49, B_50, D_55]: (k1_funct_1('#skF_6'(A_49, B_50), D_55)=B_50 | ~r2_hidden(D_55, A_49))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.56/4.44  tff(c_30107, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, k1_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden(D_55, A_49))), inference(superposition, [status(thm), theory('equality')], [c_36, c_30102])).
% 12.56/4.44  tff(c_30113, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30107])).
% 12.56/4.44  tff(c_30329, plain, (![B_50, A_6025, A_6023]: (r2_hidden(B_50, k2_relat_1('#skF_6'(k1_xboole_0, B_50))) | ~r2_hidden(A_6025, A_6023) | k1_xboole_0!=A_6023)), inference(resolution, [status(thm)], [c_30327, c_30113])).
% 12.56/4.44  tff(c_30340, plain, (![B_50, A_6025, A_6023]: (r2_hidden(B_50, k1_xboole_0) | ~r2_hidden(A_6025, A_6023) | k1_xboole_0!=A_6023)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_30329])).
% 12.56/4.44  tff(c_30346, plain, (![A_6025, A_6023]: (~r2_hidden(A_6025, A_6023) | k1_xboole_0!=A_6023)), inference(splitLeft, [status(thm)], [c_30340])).
% 12.56/4.44  tff(c_30775, plain, (![A_6073, C_6074, B_6075]: (k1_xboole_0!=A_6073 | ~r2_hidden(C_6074, k2_relat_1('#skF_6'(A_6073, B_6075))))), inference(resolution, [status(thm)], [c_30744, c_30346])).
% 12.56/4.44  tff(c_30828, plain, (![A_6076, B_6077, B_6078]: (k1_xboole_0!=A_6076 | r1_tarski(k2_relat_1('#skF_6'(A_6076, B_6077)), B_6078))), inference(resolution, [status(thm)], [c_6, c_30775])).
% 12.56/4.44  tff(c_30130, plain, (![B_5984, A_5985, D_5986]: (r2_hidden(B_5984, k2_relat_1('#skF_6'(A_5985, B_5984))) | ~r2_hidden(D_5986, A_5985))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30107])).
% 12.56/4.44  tff(c_30143, plain, (![B_5987, A_5988, B_5989]: (r2_hidden(B_5987, k2_relat_1('#skF_6'(A_5988, B_5987))) | r1_tarski(A_5988, B_5989))), inference(resolution, [status(thm)], [c_6, c_30130])).
% 12.56/4.44  tff(c_30154, plain, (![B_50, A_49, B_5989]: (r2_hidden(B_50, k1_xboole_0) | r1_tarski(A_49, B_5989) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_69, c_30143])).
% 12.56/4.44  tff(c_30190, plain, (![A_5992, B_5993]: (r1_tarski(A_5992, B_5993) | k1_xboole_0!=A_5992)), inference(splitLeft, [status(thm)], [c_30154])).
% 12.56/4.44  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.56/4.44  tff(c_30200, plain, (![B_5993, A_5992]: (B_5993=A_5992 | ~r1_tarski(B_5993, A_5992) | k1_xboole_0!=A_5992)), inference(resolution, [status(thm)], [c_30190, c_8])).
% 12.56/4.44  tff(c_30867, plain, (![B_6077]: (k2_relat_1('#skF_6'(k1_xboole_0, B_6077))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30828, c_30200])).
% 12.56/4.44  tff(c_30262, plain, (![A_6011, B_6012]: (r2_hidden('#skF_3'(A_6011, B_6012), k1_relat_1(A_6011)) | r2_hidden('#skF_4'(A_6011, B_6012), B_6012) | k2_relat_1(A_6011)=B_6012 | ~v1_funct_1(A_6011) | ~v1_relat_1(A_6011))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.56/4.44  tff(c_30273, plain, (![A_49, B_50, B_6012]: (r2_hidden('#skF_3'('#skF_6'(A_49, B_50), B_6012), A_49) | r2_hidden('#skF_4'('#skF_6'(A_49, B_50), B_6012), B_6012) | k2_relat_1('#skF_6'(A_49, B_50))=B_6012 | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_30262])).
% 12.56/4.44  tff(c_31416, plain, (![A_6133, B_6134, B_6135]: (r2_hidden('#skF_3'('#skF_6'(A_6133, B_6134), B_6135), A_6133) | r2_hidden('#skF_4'('#skF_6'(A_6133, B_6134), B_6135), B_6135) | k2_relat_1('#skF_6'(A_6133, B_6134))=B_6135)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30273])).
% 12.56/4.44  tff(c_22, plain, (![A_9, C_45]: (r2_hidden('#skF_5'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.56/4.44  tff(c_30385, plain, (![A_6028, A_6029]: (~r2_hidden(A_6028, A_6029) | k1_xboole_0!=A_6029)), inference(splitLeft, [status(thm)], [c_30340])).
% 12.56/4.44  tff(c_30492, plain, (![A_6047, C_6048]: (k1_relat_1(A_6047)!=k1_xboole_0 | ~r2_hidden(C_6048, k2_relat_1(A_6047)) | ~v1_funct_1(A_6047) | ~v1_relat_1(A_6047))), inference(resolution, [status(thm)], [c_22, c_30385])).
% 12.56/4.44  tff(c_30523, plain, (![A_49, B_50, C_6048]: (k1_relat_1('#skF_6'(A_49, B_50))!=k1_xboole_0 | ~r2_hidden(C_6048, k1_xboole_0) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_69, c_30492])).
% 12.56/4.44  tff(c_30539, plain, (![C_6048, A_49]: (~r2_hidden(C_6048, k1_xboole_0) | k1_xboole_0!=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30523])).
% 12.56/4.44  tff(c_30549, plain, (![A_49]: (k1_xboole_0!=A_49)), inference(splitLeft, [status(thm)], [c_30539])).
% 12.56/4.44  tff(c_30561, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_30549])).
% 12.56/4.44  tff(c_30562, plain, (![C_6048]: (~r2_hidden(C_6048, k1_xboole_0))), inference(splitRight, [status(thm)], [c_30539])).
% 12.56/4.44  tff(c_31431, plain, (![B_6134, B_6135]: (r2_hidden('#skF_4'('#skF_6'(k1_xboole_0, B_6134), B_6135), B_6135) | k2_relat_1('#skF_6'(k1_xboole_0, B_6134))=B_6135)), inference(resolution, [status(thm)], [c_31416, c_30562])).
% 12.56/4.44  tff(c_31479, plain, (![B_6134, B_6135]: (r2_hidden('#skF_4'('#skF_6'(k1_xboole_0, B_6134), B_6135), B_6135) | k1_xboole_0=B_6135)), inference(demodulation, [status(thm), theory('equality')], [c_30867, c_31431])).
% 12.56/4.44  tff(c_30129, plain, (![A_49, B_50, C_5983]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_5983), A_49) | ~r2_hidden(C_5983, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30124])).
% 12.56/4.44  tff(c_30159, plain, (![A_5990, C_5991]: (k1_funct_1(A_5990, '#skF_5'(A_5990, k2_relat_1(A_5990), C_5991))=C_5991 | ~r2_hidden(C_5991, k2_relat_1(A_5990)) | ~v1_funct_1(A_5990) | ~v1_relat_1(A_5990))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.56/4.44  tff(c_30176, plain, (![C_5991, B_50, A_49]: (C_5991=B_50 | ~r2_hidden(C_5991, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_5991), A_49))), inference(superposition, [status(thm), theory('equality')], [c_36, c_30159])).
% 12.56/4.44  tff(c_32228, plain, (![C_6159, B_6160, A_6161]: (C_6159=B_6160 | ~r2_hidden(C_6159, k2_relat_1('#skF_6'(A_6161, B_6160))) | ~r2_hidden('#skF_5'('#skF_6'(A_6161, B_6160), k2_relat_1('#skF_6'(A_6161, B_6160)), C_6159), A_6161))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30176])).
% 12.56/4.44  tff(c_32242, plain, (![C_6162, B_6163, A_6164]: (C_6162=B_6163 | ~r2_hidden(C_6162, k2_relat_1('#skF_6'(A_6164, B_6163))))), inference(resolution, [status(thm)], [c_30129, c_32228])).
% 12.56/4.44  tff(c_39252, plain, (![A_8604, B_8605, B_8606]: ('#skF_1'(k2_relat_1('#skF_6'(A_8604, B_8605)), B_8606)=B_8605 | r1_tarski(k2_relat_1('#skF_6'(A_8604, B_8605)), B_8606))), inference(resolution, [status(thm)], [c_6, c_32242])).
% 12.56/4.44  tff(c_46, plain, (![C_59]: (~r1_tarski(k2_relat_1(C_59), '#skF_7') | k1_relat_1(C_59)!='#skF_8' | ~v1_funct_1(C_59) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.56/4.44  tff(c_39362, plain, (![A_8604, B_8605]: (k1_relat_1('#skF_6'(A_8604, B_8605))!='#skF_8' | ~v1_funct_1('#skF_6'(A_8604, B_8605)) | ~v1_relat_1('#skF_6'(A_8604, B_8605)) | '#skF_1'(k2_relat_1('#skF_6'(A_8604, B_8605)), '#skF_7')=B_8605)), inference(resolution, [status(thm)], [c_39252, c_46])).
% 12.56/4.44  tff(c_39479, plain, (![A_8624, B_8625]: (A_8624!='#skF_8' | '#skF_1'(k2_relat_1('#skF_6'(A_8624, B_8625)), '#skF_7')=B_8625)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_39362])).
% 12.56/4.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.56/4.44  tff(c_39632, plain, (![B_8662, A_8663]: (~r2_hidden(B_8662, '#skF_7') | r1_tarski(k2_relat_1('#skF_6'(A_8663, B_8662)), '#skF_7') | A_8663!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_39479, c_4])).
% 12.56/4.44  tff(c_39665, plain, (![A_8663, B_8662]: (k1_relat_1('#skF_6'(A_8663, B_8662))!='#skF_8' | ~v1_funct_1('#skF_6'(A_8663, B_8662)) | ~v1_relat_1('#skF_6'(A_8663, B_8662)) | ~r2_hidden(B_8662, '#skF_7') | A_8663!='#skF_8')), inference(resolution, [status(thm)], [c_39632, c_46])).
% 12.56/4.44  tff(c_39736, plain, (![B_8662, A_8663]: (~r2_hidden(B_8662, '#skF_7') | A_8663!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_39665])).
% 12.56/4.44  tff(c_39744, plain, (![A_8663]: (A_8663!='#skF_8')), inference(splitLeft, [status(thm)], [c_39736])).
% 12.56/4.44  tff(c_39748, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_39744])).
% 12.56/4.44  tff(c_39750, plain, (![B_8681]: (~r2_hidden(B_8681, '#skF_7'))), inference(splitRight, [status(thm)], [c_39736])).
% 12.56/4.44  tff(c_39774, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_31479, c_39750])).
% 12.56/4.44  tff(c_39810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_39774])).
% 12.56/4.44  tff(c_39813, plain, (![B_8699]: (r2_hidden(B_8699, k1_xboole_0))), inference(splitRight, [status(thm)], [c_30340])).
% 12.56/4.44  tff(c_39833, plain, (![A_1]: (r1_tarski(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_39813, c_4])).
% 12.56/4.44  tff(c_134, plain, (![B_89, A_90]: (r2_hidden(k1_funct_1(B_89, A_90), k2_relat_1(B_89)) | ~r2_hidden(A_90, k1_relat_1(B_89)) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.56/4.44  tff(c_139, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, k1_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden(D_55, A_49))), inference(superposition, [status(thm), theory('equality')], [c_36, c_134])).
% 12.56/4.44  tff(c_148, plain, (![B_91, A_92, D_93]: (r2_hidden(B_91, k2_relat_1('#skF_6'(A_92, B_91))) | ~r2_hidden(D_93, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_139])).
% 12.56/4.44  tff(c_158, plain, (![B_94, A_95, B_96]: (r2_hidden(B_94, k2_relat_1('#skF_6'(A_95, B_94))) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_6, c_148])).
% 12.56/4.44  tff(c_169, plain, (![B_50, A_49, B_96]: (r2_hidden(B_50, k1_xboole_0) | r1_tarski(A_49, B_96) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_69, c_158])).
% 12.56/4.44  tff(c_174, plain, (![B_96]: (r1_tarski(k1_xboole_0, B_96))), inference(splitLeft, [status(thm)], [c_169])).
% 12.56/4.44  tff(c_80, plain, (![C_72]: (~r1_tarski(k2_relat_1(C_72), '#skF_7') | k1_relat_1(C_72)!='#skF_8' | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.56/4.44  tff(c_83, plain, (![A_49, B_50]: (~r1_tarski(k1_xboole_0, '#skF_7') | k1_relat_1('#skF_6'(A_49, B_50))!='#skF_8' | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_69, c_80])).
% 12.56/4.44  tff(c_85, plain, (![A_49]: (~r1_tarski(k1_xboole_0, '#skF_7') | A_49!='#skF_8' | k1_xboole_0!=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_83])).
% 12.56/4.44  tff(c_86, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(splitLeft, [status(thm)], [c_85])).
% 12.56/4.44  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_86])).
% 12.56/4.44  tff(c_178, plain, (![B_50]: (r2_hidden(B_50, k1_xboole_0))), inference(splitRight, [status(thm)], [c_169])).
% 12.56/4.44  tff(c_192, plain, (![A_98, C_99]: (k1_funct_1(A_98, '#skF_5'(A_98, k2_relat_1(A_98), C_99))=C_99 | ~r2_hidden(C_99, k2_relat_1(A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.56/4.44  tff(c_209, plain, (![C_99, B_50, A_49]: (C_99=B_50 | ~r2_hidden(C_99, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_99), A_49))), inference(superposition, [status(thm), theory('equality')], [c_36, c_192])).
% 12.56/4.44  tff(c_17798, plain, (![C_3303, B_3304, A_3305]: (C_3303=B_3304 | ~r2_hidden(C_3303, k2_relat_1('#skF_6'(A_3305, B_3304))) | ~r2_hidden('#skF_5'('#skF_6'(A_3305, B_3304), k2_relat_1('#skF_6'(A_3305, B_3304)), C_3303), A_3305))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_209])).
% 12.56/4.44  tff(c_17833, plain, (![C_3303, B_3304]: (C_3303=B_3304 | ~r2_hidden(C_3303, k2_relat_1('#skF_6'(k1_xboole_0, B_3304))))), inference(resolution, [status(thm)], [c_178, c_17798])).
% 12.56/4.44  tff(c_17842, plain, (![C_3340, B_3341]: (C_3340=B_3341)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_70, c_17833])).
% 12.56/4.44  tff(c_29478, plain, (![B_3341]: (B_3341!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17842, c_51])).
% 12.56/4.44  tff(c_30042, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_29478])).
% 12.56/4.44  tff(c_30044, plain, (r1_tarski(k1_xboole_0, '#skF_7')), inference(splitRight, [status(thm)], [c_85])).
% 12.56/4.44  tff(c_30061, plain, (![B_5967, A_5968]: (B_5967=A_5968 | ~r1_tarski(B_5967, A_5968) | ~r1_tarski(A_5968, B_5967))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.56/4.44  tff(c_30063, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_30044, c_30061])).
% 12.56/4.44  tff(c_30068, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_51, c_30063])).
% 12.56/4.44  tff(c_39865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39833, c_30068])).
% 12.56/4.44  tff(c_39867, plain, (![B_8702]: (r2_hidden(B_8702, k1_xboole_0))), inference(splitRight, [status(thm)], [c_30154])).
% 12.56/4.44  tff(c_39879, plain, (![A_1]: (r1_tarski(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_39867, c_4])).
% 12.56/4.44  tff(c_39882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39879, c_30068])).
% 12.56/4.44  tff(c_39883, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_48])).
% 12.56/4.44  tff(c_16, plain, (![A_8]: (k2_relat_1(A_8)=k1_xboole_0 | k1_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.56/4.44  tff(c_39908, plain, (![A_8710]: (k2_relat_1(A_8710)='#skF_8' | k1_relat_1(A_8710)!='#skF_8' | ~v1_relat_1(A_8710))), inference(demodulation, [status(thm), theory('equality')], [c_39883, c_39883, c_16])).
% 12.56/4.44  tff(c_39911, plain, (![A_49, B_50]: (k2_relat_1('#skF_6'(A_49, B_50))='#skF_8' | k1_relat_1('#skF_6'(A_49, B_50))!='#skF_8')), inference(resolution, [status(thm)], [c_42, c_39908])).
% 12.56/4.44  tff(c_39913, plain, (![A_49, B_50]: (k2_relat_1('#skF_6'(A_49, B_50))='#skF_8' | A_49!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_39911])).
% 12.56/4.44  tff(c_39884, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_48])).
% 12.56/4.44  tff(c_39890, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_39883, c_39884])).
% 12.56/4.44  tff(c_39938, plain, (![C_8716]: (~r1_tarski(k2_relat_1(C_8716), '#skF_8') | k1_relat_1(C_8716)!='#skF_8' | ~v1_funct_1(C_8716) | ~v1_relat_1(C_8716))), inference(demodulation, [status(thm), theory('equality')], [c_39890, c_46])).
% 12.56/4.44  tff(c_39941, plain, (![A_49, B_50]: (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_6'(A_49, B_50))!='#skF_8' | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | A_49!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_39913, c_39938])).
% 12.56/4.44  tff(c_39943, plain, (![A_49]: (A_49!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_12, c_39941])).
% 12.56/4.44  tff(c_39949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39943, c_39890])).
% 12.56/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.56/4.44  
% 12.56/4.44  Inference rules
% 12.56/4.44  ----------------------
% 12.56/4.44  #Ref     : 11
% 12.56/4.44  #Sup     : 7715
% 12.56/4.44  #Fact    : 2
% 12.56/4.44  #Define  : 0
% 12.56/4.44  #Split   : 10
% 12.56/4.44  #Chain   : 0
% 12.56/4.44  #Close   : 0
% 12.56/4.44  
% 12.56/4.44  Ordering : KBO
% 12.56/4.44  
% 12.56/4.44  Simplification rules
% 12.56/4.44  ----------------------
% 12.56/4.44  #Subsume      : 2064
% 12.56/4.44  #Demod        : 1490
% 12.56/4.44  #Tautology    : 487
% 12.56/4.44  #SimpNegUnit  : 121
% 12.56/4.44  #BackRed      : 12
% 12.56/4.44  
% 12.56/4.44  #Partial instantiations: 5640
% 12.56/4.44  #Strategies tried      : 1
% 12.56/4.44  
% 12.56/4.44  Timing (in seconds)
% 12.56/4.44  ----------------------
% 12.56/4.44  Preprocessing        : 0.39
% 12.56/4.44  Parsing              : 0.21
% 12.56/4.44  CNF conversion       : 0.03
% 12.56/4.44  Main loop            : 3.21
% 12.56/4.44  Inferencing          : 1.00
% 12.56/4.44  Reduction            : 0.90
% 12.56/4.44  Demodulation         : 0.63
% 12.56/4.44  BG Simplification    : 0.13
% 12.56/4.44  Subsumption          : 0.97
% 12.56/4.44  Abstraction          : 0.14
% 12.56/4.44  MUC search           : 0.00
% 12.59/4.44  Cooper               : 0.00
% 12.59/4.44  Total                : 3.65
% 12.59/4.44  Index Insertion      : 0.00
% 12.59/4.44  Index Deletion       : 0.00
% 12.59/4.44  Index Matching       : 0.00
% 12.59/4.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
