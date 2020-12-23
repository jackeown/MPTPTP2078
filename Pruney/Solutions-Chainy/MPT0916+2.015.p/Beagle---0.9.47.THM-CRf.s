%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:12 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 570 expanded)
%              Number of leaves         :   34 ( 195 expanded)
%              Depth                    :    9
%              Number of atoms          :  318 (1572 expanded)
%              Number of equality atoms :  100 ( 453 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_52,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_962,plain,(
    ! [A_238,C_239,B_240] :
      ( r2_hidden(k2_mcart_1(A_238),C_239)
      | ~ r2_hidden(A_238,k2_zfmisc_1(B_240,C_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1271,plain,(
    ! [B_305,C_306] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_305,C_306))),C_306)
      | v1_xboole_0(k2_zfmisc_1(B_305,C_306)) ) ),
    inference(resolution,[status(thm)],[c_4,c_962])).

tff(c_821,plain,(
    ! [A_202,C_203,B_204] :
      ( r2_hidden(k2_mcart_1(A_202),C_203)
      | ~ r2_hidden(A_202,k2_zfmisc_1(B_204,C_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_892,plain,(
    ! [B_225,C_226] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_225,C_226))),C_226)
      | v1_xboole_0(k2_zfmisc_1(B_225,C_226)) ) ),
    inference(resolution,[status(thm)],[c_4,c_821])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_628,plain,(
    ! [C_162,B_163,A_164] :
      ( ~ v1_xboole_0(C_162)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(C_162))
      | ~ r2_hidden(A_164,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_635,plain,(
    ! [A_164] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_164,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_628])).

tff(c_638,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_637,plain,(
    ! [A_164] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_164,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_628])).

tff(c_646,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_637])).

tff(c_28,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_648,plain,(
    ! [A_168,C_169,B_170] :
      ( r2_hidden(k2_mcart_1(A_168),C_169)
      | ~ r2_hidden(A_168,k2_zfmisc_1(B_170,C_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_655,plain,(
    ! [A_171,C_172,A_173,B_174] :
      ( r2_hidden(k2_mcart_1(A_171),C_172)
      | ~ r2_hidden(A_171,k3_zfmisc_1(A_173,B_174,C_172)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_648])).

tff(c_662,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_655])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_636,plain,(
    ! [A_164] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_164,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_628])).

tff(c_647,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_636])).

tff(c_30,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_667,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k7_mcart_1(A_175,B_176,C_177,D_178) = k2_mcart_1(D_178)
      | ~ m1_subset_1(D_178,k3_zfmisc_1(A_175,B_176,C_177))
      | k1_xboole_0 = C_177
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_671,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_667])).

tff(c_704,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_601,plain,(
    ! [B_156,A_157] :
      ( ~ r1_xboole_0(B_156,A_157)
      | ~ r1_tarski(B_156,A_157)
      | v1_xboole_0(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_606,plain,(
    ! [A_158] :
      ( ~ r1_tarski(A_158,k1_xboole_0)
      | v1_xboole_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_8,c_601])).

tff(c_611,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_606])).

tff(c_706,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_611])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_647,c_706])).

tff(c_712,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_759,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_463,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_hidden(k1_mcart_1(A_122),B_123)
      | ~ r2_hidden(A_122,k2_zfmisc_1(B_123,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_504,plain,(
    ! [B_136,C_137] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_136,C_137))),B_136)
      | v1_xboole_0(k2_zfmisc_1(B_136,C_137)) ) ),
    inference(resolution,[status(thm)],[c_4,c_463])).

tff(c_61,plain,(
    ! [A_42,C_43,B_44] :
      ( r2_hidden(k2_mcart_1(A_42),C_43)
      | ~ r2_hidden(A_42,k2_zfmisc_1(B_44,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_425,plain,(
    ! [B_119,C_120] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_119,C_120))),C_120)
      | v1_xboole_0(k2_zfmisc_1(B_119,C_120)) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_26,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_66,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ v1_xboole_0(C_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_47,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_66])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_75,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_47,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_66])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_74,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_47,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_77,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_103,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k7_mcart_1(A_54,B_55,C_56,D_57) = k2_mcart_1(D_57)
      | ~ m1_subset_1(D_57,k3_zfmisc_1(A_54,B_55,C_56))
      | k1_xboole_0 = C_56
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_120,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_50,plain,(
    ! [B_39,A_40] :
      ( ~ r1_xboole_0(B_39,A_40)
      | ~ r1_tarski(B_39,A_40)
      | v1_xboole_0(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [A_41] :
      ( ~ r1_tarski(A_41,k1_xboole_0)
      | v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_122,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_122])).

tff(c_129,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_160,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k6_mcart_1(A_69,B_70,C_71,D_72) = k2_mcart_1(k1_mcart_1(D_72))
      | ~ m1_subset_1(D_72,k3_zfmisc_1(A_69,B_70,C_71))
      | k1_xboole_0 = C_71
      | k1_xboole_0 = B_70
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_163,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_160])).

tff(c_166,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_163])).

tff(c_288,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_293,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_60])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_293])).

tff(c_300,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_240,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k5_mcart_1(A_84,B_85,C_86,D_87) = k1_mcart_1(k1_mcart_1(D_87))
      | ~ m1_subset_1(D_87,k3_zfmisc_1(A_84,B_85,C_86))
      | k1_xboole_0 = C_86
      | k1_xboole_0 = B_85
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_246,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_240])).

tff(c_249,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_246])).

tff(c_311,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_249])).

tff(c_312,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_318,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_60])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_318])).

tff(c_324,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_84,plain,(
    ! [A_51,B_52,C_53] : k2_zfmisc_1(k2_zfmisc_1(A_51,B_52),C_53) = k3_zfmisc_1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k1_mcart_1(A_15),B_16)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_251,plain,(
    ! [A_88,A_89,B_90,C_91] :
      ( r2_hidden(k1_mcart_1(A_88),k2_zfmisc_1(A_89,B_90))
      | ~ r2_hidden(A_88,k3_zfmisc_1(A_89,B_90,C_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_18])).

tff(c_269,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_251])).

tff(c_277,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_269,c_18])).

tff(c_326,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_277])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_326])).

tff(c_329,plain,(
    ! [A_47] : ~ r2_hidden(A_47,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_447,plain,(
    ! [B_119] : v1_xboole_0(k2_zfmisc_1(B_119,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_425,c_329])).

tff(c_354,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k1_mcart_1(A_96),B_97)
      | ~ r2_hidden(A_96,k2_zfmisc_1(B_97,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_378,plain,(
    ! [B_107,C_108] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_107,C_108))),B_107)
      | v1_xboole_0(k2_zfmisc_1(B_107,C_108)) ) ),
    inference(resolution,[status(thm)],[c_4,c_354])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_407,plain,(
    ! [B_110,C_111] :
      ( ~ v1_xboole_0(B_110)
      | v1_xboole_0(k2_zfmisc_1(B_110,C_111)) ) ),
    inference(resolution,[status(thm)],[c_378,c_2])).

tff(c_411,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_112,B_113))
      | v1_xboole_0(k3_zfmisc_1(A_112,B_113,C_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_407])).

tff(c_43,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_415,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_411,c_43])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_415])).

tff(c_454,plain,(
    ! [A_47] : ~ r2_hidden(A_47,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_527,plain,(
    ! [C_137] : v1_xboole_0(k2_zfmisc_1('#skF_5',C_137)) ),
    inference(resolution,[status(thm)],[c_504,c_454])).

tff(c_533,plain,(
    ! [B_139,C_140] :
      ( ~ v1_xboole_0(B_139)
      | v1_xboole_0(k2_zfmisc_1(B_139,C_140)) ) ),
    inference(resolution,[status(thm)],[c_504,c_2])).

tff(c_537,plain,(
    ! [A_141,B_142,C_143] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_141,B_142))
      | v1_xboole_0(k3_zfmisc_1(A_141,B_142,C_143)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_533])).

tff(c_540,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_537,c_43])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_540])).

tff(c_545,plain,(
    ! [A_47] : ~ r2_hidden(A_47,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_547,plain,(
    ! [A_144,B_145,C_146] : k2_zfmisc_1(k2_zfmisc_1(A_144,B_145),C_146) = k3_zfmisc_1(A_144,B_145,C_146) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_15,C_17,B_16] :
      ( r2_hidden(k2_mcart_1(A_15),C_17)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_579,plain,(
    ! [A_151,C_152,A_153,B_154] :
      ( r2_hidden(k2_mcart_1(A_151),C_152)
      | ~ r2_hidden(A_151,k3_zfmisc_1(A_153,B_154,C_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_16])).

tff(c_584,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_579])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_584])).

tff(c_590,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_612,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_772,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_612])).

tff(c_775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_772])).

tff(c_776,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_778,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_776])).

tff(c_782,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_611])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_782])).

tff(c_788,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_776])).

tff(c_802,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_611])).

tff(c_807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_802])).

tff(c_808,plain,(
    ! [A_164] : ~ r2_hidden(A_164,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_636])).

tff(c_591,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_808,c_591])).

tff(c_812,plain,(
    ! [A_164] : ~ r2_hidden(A_164,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_914,plain,(
    ! [B_225] : v1_xboole_0(k2_zfmisc_1(B_225,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_892,c_812])).

tff(c_639,plain,(
    ! [A_165,B_166,C_167] :
      ( r2_hidden(k1_mcart_1(A_165),B_166)
      | ~ r2_hidden(A_165,k2_zfmisc_1(B_166,C_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_845,plain,(
    ! [B_213,C_214] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_213,C_214))),B_213)
      | v1_xboole_0(k2_zfmisc_1(B_213,C_214)) ) ),
    inference(resolution,[status(thm)],[c_4,c_639])).

tff(c_874,plain,(
    ! [B_216,C_217] :
      ( ~ v1_xboole_0(B_216)
      | v1_xboole_0(k2_zfmisc_1(B_216,C_217)) ) ),
    inference(resolution,[status(thm)],[c_845,c_2])).

tff(c_878,plain,(
    ! [A_218,B_219,C_220] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_218,B_219))
      | v1_xboole_0(k3_zfmisc_1(A_218,B_219,C_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_874])).

tff(c_882,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_878,c_43])).

tff(c_920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_882])).

tff(c_921,plain,(
    ! [A_164] : ~ r2_hidden(A_164,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_931,plain,(
    ! [A_228,C_229,B_230] :
      ( r2_hidden(k2_mcart_1(A_228),C_229)
      | ~ r2_hidden(A_228,k2_zfmisc_1(B_230,C_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_945,plain,(
    ! [A_234,C_235,A_236,B_237] :
      ( r2_hidden(k2_mcart_1(A_234),C_235)
      | ~ r2_hidden(A_234,k3_zfmisc_1(A_236,B_237,C_235)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_931])).

tff(c_950,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_945])).

tff(c_955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_921,c_950])).

tff(c_956,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_991,plain,(
    ! [C_247,B_248,A_249] :
      ( ~ v1_xboole_0(C_247)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(C_247))
      | ~ r2_hidden(A_249,B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_998,plain,(
    ! [A_249] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_249,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_991])).

tff(c_1001,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_999,plain,(
    ! [A_249] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_249,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_991])).

tff(c_1002,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_999])).

tff(c_1037,plain,(
    ! [A_256,B_257,C_258,D_259] :
      ( k7_mcart_1(A_256,B_257,C_258,D_259) = k2_mcart_1(D_259)
      | ~ m1_subset_1(D_259,k3_zfmisc_1(A_256,B_257,C_258))
      | k1_xboole_0 = C_258
      | k1_xboole_0 = B_257
      | k1_xboole_0 = A_256 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1041,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_1037])).

tff(c_1074,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1041])).

tff(c_1076,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_611])).

tff(c_1081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1002,c_1076])).

tff(c_1083,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_1000,plain,(
    ! [A_249] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_249,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_991])).

tff(c_1003,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1101,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( k5_mcart_1(A_272,B_273,C_274,D_275) = k1_mcart_1(k1_mcart_1(D_275))
      | ~ m1_subset_1(D_275,k3_zfmisc_1(A_272,B_273,C_274))
      | k1_xboole_0 = C_274
      | k1_xboole_0 = B_273
      | k1_xboole_0 = A_272 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1104,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_1101])).

tff(c_1107,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1083,c_1104])).

tff(c_1115,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_1119,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_611])).

tff(c_1124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_1119])).

tff(c_1126,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_1148,plain,(
    ! [A_280,B_281,C_282,D_283] :
      ( k6_mcart_1(A_280,B_281,C_282,D_283) = k2_mcart_1(k1_mcart_1(D_283))
      | ~ m1_subset_1(D_283,k3_zfmisc_1(A_280,B_281,C_282))
      | k1_xboole_0 = C_282
      | k1_xboole_0 = B_281
      | k1_xboole_0 = A_280 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1151,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_1148])).

tff(c_1154,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1083,c_1126,c_1151])).

tff(c_1170,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1154])).

tff(c_1176,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_611])).

tff(c_1181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1001,c_1176])).

tff(c_1182,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1154])).

tff(c_984,plain,(
    ! [A_244,B_245,C_246] :
      ( r2_hidden(k1_mcart_1(A_244),B_245)
      | ~ r2_hidden(A_244,k2_zfmisc_1(B_245,C_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1132,plain,(
    ! [A_276,A_277,B_278,C_279] :
      ( r2_hidden(k1_mcart_1(A_276),k2_zfmisc_1(A_277,B_278))
      | ~ r2_hidden(A_276,k3_zfmisc_1(A_277,B_278,C_279)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_984])).

tff(c_1147,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_1132])).

tff(c_1164,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1147,c_16])).

tff(c_1184,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_1164])).

tff(c_1186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_956,c_1184])).

tff(c_1187,plain,(
    ! [A_249] : ~ r2_hidden(A_249,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_1292,plain,(
    ! [B_305] : v1_xboole_0(k2_zfmisc_1(B_305,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_1271,c_1187])).

tff(c_1222,plain,(
    ! [B_293,C_294] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_293,C_294))),B_293)
      | v1_xboole_0(k2_zfmisc_1(B_293,C_294)) ) ),
    inference(resolution,[status(thm)],[c_4,c_984])).

tff(c_1251,plain,(
    ! [B_296,C_297] :
      ( ~ v1_xboole_0(B_296)
      | v1_xboole_0(k2_zfmisc_1(B_296,C_297)) ) ),
    inference(resolution,[status(thm)],[c_1222,c_2])).

tff(c_1262,plain,(
    ! [A_302,B_303,C_304] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_302,B_303))
      | v1_xboole_0(k3_zfmisc_1(A_302,B_303,C_304)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1251])).

tff(c_1266,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1262,c_43])).

tff(c_1300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_1266])).

tff(c_1301,plain,(
    ! [A_249] : ~ r2_hidden(A_249,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_999])).

tff(c_1304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1301,c_591])).

tff(c_1305,plain,(
    ! [A_249] : ~ r2_hidden(A_249,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_957,plain,(
    r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_1308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1305,c_957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/2.15  
% 4.33/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/2.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 4.33/2.15  
% 4.33/2.15  %Foreground sorts:
% 4.33/2.15  
% 4.33/2.15  
% 4.33/2.15  %Background operators:
% 4.33/2.15  
% 4.33/2.15  
% 4.33/2.15  %Foreground operators:
% 4.33/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.33/2.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.33/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.33/2.15  tff('#skF_7', type, '#skF_7': $i).
% 4.33/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/2.15  tff('#skF_5', type, '#skF_5': $i).
% 4.33/2.15  tff('#skF_6', type, '#skF_6': $i).
% 4.33/2.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.33/2.15  tff('#skF_2', type, '#skF_2': $i).
% 4.33/2.15  tff('#skF_3', type, '#skF_3': $i).
% 4.33/2.15  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.33/2.15  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.33/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.33/2.15  tff('#skF_8', type, '#skF_8': $i).
% 4.33/2.15  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.33/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/2.15  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.33/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.33/2.15  tff('#skF_4', type, '#skF_4': $i).
% 4.33/2.15  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.33/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/2.15  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.33/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.33/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.33/2.15  
% 4.33/2.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.33/2.20  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.33/2.20  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 4.33/2.20  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.33/2.20  tff(f_52, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.33/2.20  tff(f_78, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.33/2.20  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.33/2.20  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.33/2.20  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.33/2.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.33/2.20  tff(c_962, plain, (![A_238, C_239, B_240]: (r2_hidden(k2_mcart_1(A_238), C_239) | ~r2_hidden(A_238, k2_zfmisc_1(B_240, C_239)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_1271, plain, (![B_305, C_306]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_305, C_306))), C_306) | v1_xboole_0(k2_zfmisc_1(B_305, C_306)))), inference(resolution, [status(thm)], [c_4, c_962])).
% 4.33/2.20  tff(c_821, plain, (![A_202, C_203, B_204]: (r2_hidden(k2_mcart_1(A_202), C_203) | ~r2_hidden(A_202, k2_zfmisc_1(B_204, C_203)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_892, plain, (![B_225, C_226]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_225, C_226))), C_226) | v1_xboole_0(k2_zfmisc_1(B_225, C_226)))), inference(resolution, [status(thm)], [c_4, c_821])).
% 4.33/2.20  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.33/2.20  tff(c_628, plain, (![C_162, B_163, A_164]: (~v1_xboole_0(C_162) | ~m1_subset_1(B_163, k1_zfmisc_1(C_162)) | ~r2_hidden(A_164, B_163))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.33/2.20  tff(c_635, plain, (![A_164]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_164, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_628])).
% 4.33/2.20  tff(c_638, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_635])).
% 4.33/2.20  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.33/2.20  tff(c_637, plain, (![A_164]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_164, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_628])).
% 4.33/2.20  tff(c_646, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_637])).
% 4.33/2.20  tff(c_28, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.33/2.20  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.33/2.20  tff(c_648, plain, (![A_168, C_169, B_170]: (r2_hidden(k2_mcart_1(A_168), C_169) | ~r2_hidden(A_168, k2_zfmisc_1(B_170, C_169)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_655, plain, (![A_171, C_172, A_173, B_174]: (r2_hidden(k2_mcart_1(A_171), C_172) | ~r2_hidden(A_171, k3_zfmisc_1(A_173, B_174, C_172)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_648])).
% 4.33/2.20  tff(c_662, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_28, c_655])).
% 4.33/2.20  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.33/2.20  tff(c_636, plain, (![A_164]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_164, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_628])).
% 4.33/2.20  tff(c_647, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_636])).
% 4.33/2.20  tff(c_30, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.33/2.20  tff(c_667, plain, (![A_175, B_176, C_177, D_178]: (k7_mcart_1(A_175, B_176, C_177, D_178)=k2_mcart_1(D_178) | ~m1_subset_1(D_178, k3_zfmisc_1(A_175, B_176, C_177)) | k1_xboole_0=C_177 | k1_xboole_0=B_176 | k1_xboole_0=A_175)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/2.20  tff(c_671, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_667])).
% 4.33/2.20  tff(c_704, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_671])).
% 4.33/2.20  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.33/2.20  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.33/2.20  tff(c_601, plain, (![B_156, A_157]: (~r1_xboole_0(B_156, A_157) | ~r1_tarski(B_156, A_157) | v1_xboole_0(B_156))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/2.20  tff(c_606, plain, (![A_158]: (~r1_tarski(A_158, k1_xboole_0) | v1_xboole_0(A_158))), inference(resolution, [status(thm)], [c_8, c_601])).
% 4.33/2.20  tff(c_611, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_606])).
% 4.33/2.20  tff(c_706, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_704, c_611])).
% 4.33/2.20  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_647, c_706])).
% 4.33/2.20  tff(c_712, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_671])).
% 4.33/2.20  tff(c_759, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_712])).
% 4.33/2.20  tff(c_463, plain, (![A_122, B_123, C_124]: (r2_hidden(k1_mcart_1(A_122), B_123) | ~r2_hidden(A_122, k2_zfmisc_1(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_504, plain, (![B_136, C_137]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_136, C_137))), B_136) | v1_xboole_0(k2_zfmisc_1(B_136, C_137)))), inference(resolution, [status(thm)], [c_4, c_463])).
% 4.33/2.20  tff(c_61, plain, (![A_42, C_43, B_44]: (r2_hidden(k2_mcart_1(A_42), C_43) | ~r2_hidden(A_42, k2_zfmisc_1(B_44, C_43)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_425, plain, (![B_119, C_120]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_119, C_120))), C_120) | v1_xboole_0(k2_zfmisc_1(B_119, C_120)))), inference(resolution, [status(thm)], [c_4, c_61])).
% 4.33/2.20  tff(c_26, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.33/2.20  tff(c_44, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_26])).
% 4.33/2.20  tff(c_66, plain, (![C_45, B_46, A_47]: (~v1_xboole_0(C_45) | ~m1_subset_1(B_46, k1_zfmisc_1(C_45)) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.33/2.20  tff(c_73, plain, (![A_47]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_47, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_66])).
% 4.33/2.20  tff(c_76, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_73])).
% 4.33/2.20  tff(c_75, plain, (![A_47]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_47, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_66])).
% 4.33/2.20  tff(c_78, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_75])).
% 4.33/2.20  tff(c_74, plain, (![A_47]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_47, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_66])).
% 4.33/2.20  tff(c_77, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 4.33/2.20  tff(c_103, plain, (![A_54, B_55, C_56, D_57]: (k7_mcart_1(A_54, B_55, C_56, D_57)=k2_mcart_1(D_57) | ~m1_subset_1(D_57, k3_zfmisc_1(A_54, B_55, C_56)) | k1_xboole_0=C_56 | k1_xboole_0=B_55 | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/2.20  tff(c_107, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_103])).
% 4.33/2.20  tff(c_120, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_107])).
% 4.33/2.20  tff(c_50, plain, (![B_39, A_40]: (~r1_xboole_0(B_39, A_40) | ~r1_tarski(B_39, A_40) | v1_xboole_0(B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/2.20  tff(c_55, plain, (![A_41]: (~r1_tarski(A_41, k1_xboole_0) | v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_8, c_50])).
% 4.33/2.20  tff(c_60, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_55])).
% 4.33/2.20  tff(c_122, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60])).
% 4.33/2.20  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_122])).
% 4.33/2.20  tff(c_129, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_107])).
% 4.33/2.20  tff(c_160, plain, (![A_69, B_70, C_71, D_72]: (k6_mcart_1(A_69, B_70, C_71, D_72)=k2_mcart_1(k1_mcart_1(D_72)) | ~m1_subset_1(D_72, k3_zfmisc_1(A_69, B_70, C_71)) | k1_xboole_0=C_71 | k1_xboole_0=B_70 | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/2.20  tff(c_163, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_160])).
% 4.33/2.20  tff(c_166, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_129, c_163])).
% 4.33/2.20  tff(c_288, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_166])).
% 4.33/2.20  tff(c_293, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_60])).
% 4.33/2.20  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_293])).
% 4.33/2.20  tff(c_300, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_166])).
% 4.33/2.20  tff(c_240, plain, (![A_84, B_85, C_86, D_87]: (k5_mcart_1(A_84, B_85, C_86, D_87)=k1_mcart_1(k1_mcart_1(D_87)) | ~m1_subset_1(D_87, k3_zfmisc_1(A_84, B_85, C_86)) | k1_xboole_0=C_86 | k1_xboole_0=B_85 | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/2.20  tff(c_246, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_240])).
% 4.33/2.20  tff(c_249, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_129, c_246])).
% 4.33/2.20  tff(c_311, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_300, c_249])).
% 4.33/2.20  tff(c_312, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_311])).
% 4.33/2.20  tff(c_318, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_60])).
% 4.33/2.20  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_318])).
% 4.33/2.20  tff(c_324, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_311])).
% 4.33/2.20  tff(c_84, plain, (![A_51, B_52, C_53]: (k2_zfmisc_1(k2_zfmisc_1(A_51, B_52), C_53)=k3_zfmisc_1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.33/2.20  tff(c_18, plain, (![A_15, B_16, C_17]: (r2_hidden(k1_mcart_1(A_15), B_16) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_251, plain, (![A_88, A_89, B_90, C_91]: (r2_hidden(k1_mcart_1(A_88), k2_zfmisc_1(A_89, B_90)) | ~r2_hidden(A_88, k3_zfmisc_1(A_89, B_90, C_91)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_18])).
% 4.33/2.20  tff(c_269, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_251])).
% 4.33/2.20  tff(c_277, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_269, c_18])).
% 4.33/2.20  tff(c_326, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_277])).
% 4.33/2.20  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_326])).
% 4.33/2.20  tff(c_329, plain, (![A_47]: (~r2_hidden(A_47, '#skF_6'))), inference(splitRight, [status(thm)], [c_75])).
% 4.33/2.20  tff(c_447, plain, (![B_119]: (v1_xboole_0(k2_zfmisc_1(B_119, '#skF_6')))), inference(resolution, [status(thm)], [c_425, c_329])).
% 4.33/2.20  tff(c_354, plain, (![A_96, B_97, C_98]: (r2_hidden(k1_mcart_1(A_96), B_97) | ~r2_hidden(A_96, k2_zfmisc_1(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_378, plain, (![B_107, C_108]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_107, C_108))), B_107) | v1_xboole_0(k2_zfmisc_1(B_107, C_108)))), inference(resolution, [status(thm)], [c_4, c_354])).
% 4.33/2.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.33/2.20  tff(c_407, plain, (![B_110, C_111]: (~v1_xboole_0(B_110) | v1_xboole_0(k2_zfmisc_1(B_110, C_111)))), inference(resolution, [status(thm)], [c_378, c_2])).
% 4.33/2.20  tff(c_411, plain, (![A_112, B_113, C_114]: (~v1_xboole_0(k2_zfmisc_1(A_112, B_113)) | v1_xboole_0(k3_zfmisc_1(A_112, B_113, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_407])).
% 4.33/2.20  tff(c_43, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_2])).
% 4.33/2.20  tff(c_415, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_411, c_43])).
% 4.33/2.20  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_415])).
% 4.33/2.20  tff(c_454, plain, (![A_47]: (~r2_hidden(A_47, '#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 4.33/2.20  tff(c_527, plain, (![C_137]: (v1_xboole_0(k2_zfmisc_1('#skF_5', C_137)))), inference(resolution, [status(thm)], [c_504, c_454])).
% 4.33/2.20  tff(c_533, plain, (![B_139, C_140]: (~v1_xboole_0(B_139) | v1_xboole_0(k2_zfmisc_1(B_139, C_140)))), inference(resolution, [status(thm)], [c_504, c_2])).
% 4.33/2.20  tff(c_537, plain, (![A_141, B_142, C_143]: (~v1_xboole_0(k2_zfmisc_1(A_141, B_142)) | v1_xboole_0(k3_zfmisc_1(A_141, B_142, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_533])).
% 4.33/2.20  tff(c_540, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_537, c_43])).
% 4.33/2.20  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_527, c_540])).
% 4.33/2.20  tff(c_545, plain, (![A_47]: (~r2_hidden(A_47, '#skF_7'))), inference(splitRight, [status(thm)], [c_73])).
% 4.33/2.20  tff(c_547, plain, (![A_144, B_145, C_146]: (k2_zfmisc_1(k2_zfmisc_1(A_144, B_145), C_146)=k3_zfmisc_1(A_144, B_145, C_146))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.33/2.20  tff(c_16, plain, (![A_15, C_17, B_16]: (r2_hidden(k2_mcart_1(A_15), C_17) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_579, plain, (![A_151, C_152, A_153, B_154]: (r2_hidden(k2_mcart_1(A_151), C_152) | ~r2_hidden(A_151, k3_zfmisc_1(A_153, B_154, C_152)))), inference(superposition, [status(thm), theory('equality')], [c_547, c_16])).
% 4.33/2.20  tff(c_584, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_28, c_579])).
% 4.33/2.20  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_584])).
% 4.33/2.20  tff(c_590, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_26])).
% 4.33/2.20  tff(c_612, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_590])).
% 4.33/2.20  tff(c_772, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_612])).
% 4.33/2.20  tff(c_775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_662, c_772])).
% 4.33/2.20  tff(c_776, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_712])).
% 4.33/2.20  tff(c_778, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_776])).
% 4.33/2.20  tff(c_782, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_778, c_611])).
% 4.33/2.20  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_782])).
% 4.33/2.20  tff(c_788, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_776])).
% 4.33/2.20  tff(c_802, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_611])).
% 4.33/2.20  tff(c_807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_638, c_802])).
% 4.33/2.20  tff(c_808, plain, (![A_164]: (~r2_hidden(A_164, '#skF_5'))), inference(splitRight, [status(thm)], [c_636])).
% 4.33/2.20  tff(c_591, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 4.33/2.20  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_808, c_591])).
% 4.33/2.20  tff(c_812, plain, (![A_164]: (~r2_hidden(A_164, '#skF_6'))), inference(splitRight, [status(thm)], [c_637])).
% 4.33/2.20  tff(c_914, plain, (![B_225]: (v1_xboole_0(k2_zfmisc_1(B_225, '#skF_6')))), inference(resolution, [status(thm)], [c_892, c_812])).
% 4.33/2.20  tff(c_639, plain, (![A_165, B_166, C_167]: (r2_hidden(k1_mcart_1(A_165), B_166) | ~r2_hidden(A_165, k2_zfmisc_1(B_166, C_167)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_845, plain, (![B_213, C_214]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_213, C_214))), B_213) | v1_xboole_0(k2_zfmisc_1(B_213, C_214)))), inference(resolution, [status(thm)], [c_4, c_639])).
% 4.33/2.20  tff(c_874, plain, (![B_216, C_217]: (~v1_xboole_0(B_216) | v1_xboole_0(k2_zfmisc_1(B_216, C_217)))), inference(resolution, [status(thm)], [c_845, c_2])).
% 4.33/2.20  tff(c_878, plain, (![A_218, B_219, C_220]: (~v1_xboole_0(k2_zfmisc_1(A_218, B_219)) | v1_xboole_0(k3_zfmisc_1(A_218, B_219, C_220)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_874])).
% 4.33/2.20  tff(c_882, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_878, c_43])).
% 4.33/2.20  tff(c_920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_914, c_882])).
% 4.33/2.20  tff(c_921, plain, (![A_164]: (~r2_hidden(A_164, '#skF_7'))), inference(splitRight, [status(thm)], [c_635])).
% 4.33/2.20  tff(c_931, plain, (![A_228, C_229, B_230]: (r2_hidden(k2_mcart_1(A_228), C_229) | ~r2_hidden(A_228, k2_zfmisc_1(B_230, C_229)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_945, plain, (![A_234, C_235, A_236, B_237]: (r2_hidden(k2_mcart_1(A_234), C_235) | ~r2_hidden(A_234, k3_zfmisc_1(A_236, B_237, C_235)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_931])).
% 4.33/2.20  tff(c_950, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_28, c_945])).
% 4.33/2.20  tff(c_955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_921, c_950])).
% 4.33/2.20  tff(c_956, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_590])).
% 4.33/2.20  tff(c_991, plain, (![C_247, B_248, A_249]: (~v1_xboole_0(C_247) | ~m1_subset_1(B_248, k1_zfmisc_1(C_247)) | ~r2_hidden(A_249, B_248))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.33/2.20  tff(c_998, plain, (![A_249]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_249, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_991])).
% 4.33/2.20  tff(c_1001, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_998])).
% 4.33/2.20  tff(c_999, plain, (![A_249]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_249, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_991])).
% 4.33/2.20  tff(c_1002, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_999])).
% 4.33/2.20  tff(c_1037, plain, (![A_256, B_257, C_258, D_259]: (k7_mcart_1(A_256, B_257, C_258, D_259)=k2_mcart_1(D_259) | ~m1_subset_1(D_259, k3_zfmisc_1(A_256, B_257, C_258)) | k1_xboole_0=C_258 | k1_xboole_0=B_257 | k1_xboole_0=A_256)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/2.20  tff(c_1041, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_1037])).
% 4.33/2.20  tff(c_1074, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1041])).
% 4.33/2.20  tff(c_1076, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_611])).
% 4.33/2.20  tff(c_1081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1002, c_1076])).
% 4.33/2.20  tff(c_1083, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1041])).
% 4.33/2.20  tff(c_1000, plain, (![A_249]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_249, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_991])).
% 4.33/2.20  tff(c_1003, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1000])).
% 4.33/2.20  tff(c_1101, plain, (![A_272, B_273, C_274, D_275]: (k5_mcart_1(A_272, B_273, C_274, D_275)=k1_mcart_1(k1_mcart_1(D_275)) | ~m1_subset_1(D_275, k3_zfmisc_1(A_272, B_273, C_274)) | k1_xboole_0=C_274 | k1_xboole_0=B_273 | k1_xboole_0=A_272)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/2.20  tff(c_1104, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_1101])).
% 4.33/2.20  tff(c_1107, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1083, c_1104])).
% 4.33/2.20  tff(c_1115, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1107])).
% 4.33/2.20  tff(c_1119, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_611])).
% 4.33/2.20  tff(c_1124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1003, c_1119])).
% 4.33/2.20  tff(c_1126, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1107])).
% 4.33/2.20  tff(c_1148, plain, (![A_280, B_281, C_282, D_283]: (k6_mcart_1(A_280, B_281, C_282, D_283)=k2_mcart_1(k1_mcart_1(D_283)) | ~m1_subset_1(D_283, k3_zfmisc_1(A_280, B_281, C_282)) | k1_xboole_0=C_282 | k1_xboole_0=B_281 | k1_xboole_0=A_280)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.33/2.20  tff(c_1151, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_1148])).
% 4.33/2.20  tff(c_1154, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1083, c_1126, c_1151])).
% 4.33/2.20  tff(c_1170, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1154])).
% 4.33/2.20  tff(c_1176, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1170, c_611])).
% 4.33/2.20  tff(c_1181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1001, c_1176])).
% 4.33/2.20  tff(c_1182, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1154])).
% 4.33/2.20  tff(c_984, plain, (![A_244, B_245, C_246]: (r2_hidden(k1_mcart_1(A_244), B_245) | ~r2_hidden(A_244, k2_zfmisc_1(B_245, C_246)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/2.20  tff(c_1132, plain, (![A_276, A_277, B_278, C_279]: (r2_hidden(k1_mcart_1(A_276), k2_zfmisc_1(A_277, B_278)) | ~r2_hidden(A_276, k3_zfmisc_1(A_277, B_278, C_279)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_984])).
% 4.33/2.20  tff(c_1147, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_1132])).
% 4.33/2.20  tff(c_1164, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1147, c_16])).
% 4.33/2.20  tff(c_1184, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_1164])).
% 4.33/2.20  tff(c_1186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_956, c_1184])).
% 4.33/2.20  tff(c_1187, plain, (![A_249]: (~r2_hidden(A_249, '#skF_6'))), inference(splitRight, [status(thm)], [c_1000])).
% 4.33/2.20  tff(c_1292, plain, (![B_305]: (v1_xboole_0(k2_zfmisc_1(B_305, '#skF_6')))), inference(resolution, [status(thm)], [c_1271, c_1187])).
% 4.33/2.20  tff(c_1222, plain, (![B_293, C_294]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_293, C_294))), B_293) | v1_xboole_0(k2_zfmisc_1(B_293, C_294)))), inference(resolution, [status(thm)], [c_4, c_984])).
% 4.33/2.20  tff(c_1251, plain, (![B_296, C_297]: (~v1_xboole_0(B_296) | v1_xboole_0(k2_zfmisc_1(B_296, C_297)))), inference(resolution, [status(thm)], [c_1222, c_2])).
% 4.33/2.20  tff(c_1262, plain, (![A_302, B_303, C_304]: (~v1_xboole_0(k2_zfmisc_1(A_302, B_303)) | v1_xboole_0(k3_zfmisc_1(A_302, B_303, C_304)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1251])).
% 4.33/2.20  tff(c_1266, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1262, c_43])).
% 4.33/2.20  tff(c_1300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1292, c_1266])).
% 4.33/2.20  tff(c_1301, plain, (![A_249]: (~r2_hidden(A_249, '#skF_5'))), inference(splitRight, [status(thm)], [c_999])).
% 4.33/2.20  tff(c_1304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1301, c_591])).
% 4.33/2.20  tff(c_1305, plain, (![A_249]: (~r2_hidden(A_249, '#skF_7'))), inference(splitRight, [status(thm)], [c_998])).
% 4.33/2.20  tff(c_957, plain, (r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_590])).
% 4.33/2.20  tff(c_1308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1305, c_957])).
% 4.33/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/2.20  
% 4.33/2.20  Inference rules
% 4.33/2.20  ----------------------
% 4.33/2.20  #Ref     : 0
% 4.33/2.20  #Sup     : 253
% 4.33/2.20  #Fact    : 0
% 4.33/2.20  #Define  : 0
% 4.33/2.20  #Split   : 33
% 4.33/2.20  #Chain   : 0
% 4.33/2.20  #Close   : 0
% 4.33/2.20  
% 4.33/2.20  Ordering : KBO
% 4.33/2.20  
% 4.33/2.20  Simplification rules
% 4.33/2.20  ----------------------
% 4.33/2.20  #Subsume      : 22
% 4.33/2.20  #Demod        : 179
% 4.33/2.20  #Tautology    : 28
% 4.33/2.20  #SimpNegUnit  : 26
% 4.33/2.20  #BackRed      : 87
% 4.33/2.20  
% 4.33/2.20  #Partial instantiations: 0
% 4.33/2.20  #Strategies tried      : 1
% 4.33/2.20  
% 4.33/2.20  Timing (in seconds)
% 4.33/2.20  ----------------------
% 4.33/2.20  Preprocessing        : 0.48
% 4.33/2.20  Parsing              : 0.25
% 4.33/2.20  CNF conversion       : 0.04
% 4.33/2.20  Main loop            : 0.78
% 4.33/2.20  Inferencing          : 0.29
% 4.33/2.20  Reduction            : 0.24
% 4.33/2.21  Demodulation         : 0.16
% 4.33/2.21  BG Simplification    : 0.04
% 4.33/2.21  Subsumption          : 0.12
% 4.33/2.21  Abstraction          : 0.04
% 4.33/2.21  MUC search           : 0.00
% 4.33/2.21  Cooper               : 0.00
% 4.33/2.21  Total                : 1.36
% 4.33/2.21  Index Insertion      : 0.00
% 4.33/2.21  Index Deletion       : 0.00
% 4.33/2.21  Index Matching       : 0.00
% 4.33/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
