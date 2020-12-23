%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:48 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  210 (2146 expanded)
%              Number of leaves         :   29 ( 833 expanded)
%              Depth                    :   25
%              Number of atoms          :  612 (10072 expanded)
%              Number of equality atoms :  104 ( 592 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_orders_2(C,A,B)
               => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m1_orders_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_40,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_137,plain,(
    ! [C_92,A_93,B_94] :
      ( m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_orders_2(C_92,A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_139,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_137])).

tff(c_142,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_139])).

tff(c_143,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_142])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_149,plain,(
    ! [A_8] :
      ( m1_subset_1(A_8,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_8,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_143,c_12])).

tff(c_49,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_1028,plain,(
    ! [A_186,B_187,C_188] :
      ( r2_hidden('#skF_2'(A_186,B_187,C_188),B_187)
      | ~ m1_orders_2(C_188,A_186,B_187)
      | k1_xboole_0 = B_187
      | ~ m1_subset_1(C_188,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_orders_2(A_186)
      | ~ v5_orders_2(A_186)
      | ~ v4_orders_2(A_186)
      | ~ v3_orders_2(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1032,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_5'),B_187)
      | ~ m1_orders_2('#skF_5','#skF_3',B_187)
      | k1_xboole_0 = B_187
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_1028])).

tff(c_1047,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_5'),B_187)
      | ~ m1_orders_2('#skF_5','#skF_3',B_187)
      | k1_xboole_0 = B_187
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1032])).

tff(c_1246,plain,(
    ! [B_221] :
      ( r2_hidden('#skF_2'('#skF_3',B_221,'#skF_5'),B_221)
      | ~ m1_orders_2('#skF_5','#skF_3',B_221)
      | k1_xboole_0 = B_221
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1047])).

tff(c_1258,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_1246])).

tff(c_1265,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1258])).

tff(c_1266,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1265])).

tff(c_277,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden('#skF_2'(A_121,B_122,C_123),B_122)
      | ~ m1_orders_2(C_123,A_121,B_122)
      | k1_xboole_0 = B_122
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_279,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_2'('#skF_3',B_122,'#skF_5'),B_122)
      | ~ m1_orders_2('#skF_5','#skF_3',B_122)
      | k1_xboole_0 = B_122
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_277])).

tff(c_290,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_2'('#skF_3',B_122,'#skF_5'),B_122)
      | ~ m1_orders_2('#skF_5','#skF_3',B_122)
      | k1_xboole_0 = B_122
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_279])).

tff(c_394,plain,(
    ! [B_140] :
      ( r2_hidden('#skF_2'('#skF_3',B_140,'#skF_5'),B_140)
      | ~ m1_orders_2('#skF_5','#skF_3',B_140)
      | k1_xboole_0 = B_140
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_290])).

tff(c_404,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_394])).

tff(c_410,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_404])).

tff(c_411,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_67,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_75,B_76,B_77] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_77)
      | ~ r1_tarski(A_75,B_77)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_85,B_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(A_85,B_86),B_87)
      | ~ r1_tarski(B_88,B_87)
      | ~ r1_tarski(A_85,B_88)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_121,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_89,'#skF_4')
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_53,c_111])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,'#skF_4')
      | r1_tarski(A_89,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_121,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_201,plain,(
    ! [C_111,A_112] :
      ( k1_xboole_0 = C_111
      | ~ m1_orders_2(C_111,A_112,k1_xboole_0)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_211,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_201])).

tff(c_220,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_211])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_220])).

tff(c_222,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_226,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_222])).

tff(c_234,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_226])).

tff(c_415,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_234])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_415])).

tff(c_424,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_475,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),B_146)
      | ~ r1_tarski('#skF_4',B_146) ) ),
    inference(resolution,[status(thm)],[c_424,c_2])).

tff(c_71,plain,(
    ! [A_68,C_69,B_70] :
      ( m1_subset_1(A_68,C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_68,B_7,A_6] :
      ( m1_subset_1(A_68,B_7)
      | ~ r2_hidden(A_68,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_524,plain,(
    ! [B_149,B_150] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),B_149)
      | ~ r1_tarski(B_150,B_149)
      | ~ r1_tarski('#skF_4',B_150) ) ),
    inference(resolution,[status(thm)],[c_475,c_76])).

tff(c_538,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_524])).

tff(c_547,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_538])).

tff(c_425,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_674,plain,(
    ! [A_161,B_162,C_163] :
      ( k3_orders_2(A_161,B_162,'#skF_2'(A_161,B_162,C_163)) = C_163
      | ~ m1_orders_2(C_163,A_161,B_162)
      | k1_xboole_0 = B_162
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_orders_2(A_161)
      | ~ v5_orders_2(A_161)
      | ~ v4_orders_2(A_161)
      | ~ v3_orders_2(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_679,plain,(
    ! [B_162] :
      ( k3_orders_2('#skF_3',B_162,'#skF_2'('#skF_3',B_162,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_162)
      | k1_xboole_0 = B_162
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_674])).

tff(c_691,plain,(
    ! [B_162] :
      ( k3_orders_2('#skF_3',B_162,'#skF_2'('#skF_3',B_162,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_162)
      | k1_xboole_0 = B_162
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_679])).

tff(c_865,plain,(
    ! [B_182] :
      ( k3_orders_2('#skF_3',B_182,'#skF_2'('#skF_3',B_182,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_182)
      | k1_xboole_0 = B_182
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_691])).

tff(c_878,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_865])).

tff(c_885,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_878])).

tff(c_886,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_885])).

tff(c_30,plain,(
    ! [B_45,D_51,A_37,C_49] :
      ( r2_hidden(B_45,D_51)
      | ~ r2_hidden(B_45,k3_orders_2(A_37,D_51,C_49))
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(C_49,u1_struct_0(A_37))
      | ~ m1_subset_1(B_45,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v5_orders_2(A_37)
      | ~ v4_orders_2(A_37)
      | ~ v3_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_891,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_30])).

tff(c_898,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_547,c_38,c_891])).

tff(c_901,plain,(
    ! [B_183] :
      ( r2_hidden(B_183,'#skF_4')
      | ~ r2_hidden(B_183,'#skF_5')
      | ~ m1_subset_1(B_183,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_898])).

tff(c_943,plain,(
    ! [A_184] :
      ( r2_hidden(A_184,'#skF_4')
      | ~ r2_hidden(A_184,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_149,c_901])).

tff(c_990,plain,(
    ! [B_185] :
      ( r2_hidden('#skF_1'('#skF_5',B_185),'#skF_4')
      | r1_tarski('#skF_5',B_185) ) ),
    inference(resolution,[status(thm)],[c_6,c_943])).

tff(c_998,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_990,c_4])).

tff(c_1004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_998])).

tff(c_1006,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_143,c_201])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_203])).

tff(c_215,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_214])).

tff(c_1069,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_215])).

tff(c_1070,plain,(
    ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1069])).

tff(c_1274,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1070])).

tff(c_1284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1274])).

tff(c_1285,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1265])).

tff(c_1320,plain,(
    ! [B_226] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),B_226)
      | ~ r1_tarski('#skF_4',B_226) ) ),
    inference(resolution,[status(thm)],[c_1285,c_2])).

tff(c_1424,plain,(
    ! [B_234,B_235] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),B_234)
      | ~ r1_tarski(B_235,B_234)
      | ~ r1_tarski('#skF_4',B_235) ) ),
    inference(resolution,[status(thm)],[c_1320,c_76])).

tff(c_1442,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_1424])).

tff(c_1453,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1442])).

tff(c_1286,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1265])).

tff(c_1393,plain,(
    ! [A_231,B_232,C_233] :
      ( k3_orders_2(A_231,B_232,'#skF_2'(A_231,B_232,C_233)) = C_233
      | ~ m1_orders_2(C_233,A_231,B_232)
      | k1_xboole_0 = B_232
      | ~ m1_subset_1(C_233,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_orders_2(A_231)
      | ~ v5_orders_2(A_231)
      | ~ v4_orders_2(A_231)
      | ~ v3_orders_2(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1400,plain,(
    ! [B_232] :
      ( k3_orders_2('#skF_3',B_232,'#skF_2'('#skF_3',B_232,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_232)
      | k1_xboole_0 = B_232
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_1393])).

tff(c_1416,plain,(
    ! [B_232] :
      ( k3_orders_2('#skF_3',B_232,'#skF_2'('#skF_3',B_232,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_232)
      | k1_xboole_0 = B_232
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1400])).

tff(c_1592,plain,(
    ! [B_245] :
      ( k3_orders_2('#skF_3',B_245,'#skF_2'('#skF_3',B_245,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_245)
      | k1_xboole_0 = B_245
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1416])).

tff(c_1607,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_1592])).

tff(c_1615,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1607])).

tff(c_1616,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1286,c_1615])).

tff(c_1621,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1616,c_30])).

tff(c_1628,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1453,c_38,c_1621])).

tff(c_1631,plain,(
    ! [B_246] :
      ( r2_hidden(B_246,'#skF_4')
      | ~ r2_hidden(B_246,'#skF_5')
      | ~ m1_subset_1(B_246,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1628])).

tff(c_1681,plain,(
    ! [A_247] :
      ( r2_hidden(A_247,'#skF_4')
      | ~ r2_hidden(A_247,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_149,c_1631])).

tff(c_1714,plain,(
    ! [B_248] :
      ( r2_hidden('#skF_1'('#skF_5',B_248),'#skF_4')
      | r1_tarski('#skF_5',B_248) ) ),
    inference(resolution,[status(thm)],[c_6,c_1681])).

tff(c_1722,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1714,c_4])).

tff(c_1728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_1722])).

tff(c_1729,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1069])).

tff(c_1040,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_4'),B_187)
      | ~ m1_orders_2('#skF_4','#skF_3',B_187)
      | k1_xboole_0 = B_187
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_1028])).

tff(c_1053,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_4'),B_187)
      | ~ m1_orders_2('#skF_4','#skF_3',B_187)
      | k1_xboole_0 = B_187
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1040])).

tff(c_1054,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_4'),B_187)
      | ~ m1_orders_2('#skF_4','#skF_3',B_187)
      | k1_xboole_0 = B_187
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1053])).

tff(c_1761,plain,(
    ! [B_253] :
      ( r2_hidden('#skF_2'('#skF_3',B_253,'#skF_4'),B_253)
      | ~ m1_orders_2('#skF_4','#skF_3',B_253)
      | B_253 = '#skF_5'
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1054])).

tff(c_1775,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_orders_2('#skF_4','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_1761])).

tff(c_1778,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1775])).

tff(c_1048,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_3',B_187,'#skF_5'),B_187)
      | ~ m1_orders_2('#skF_5','#skF_3',B_187)
      | k1_xboole_0 = B_187
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1047])).

tff(c_1840,plain,(
    ! [B_266] :
      ( r2_hidden('#skF_2'('#skF_3',B_266,'#skF_5'),B_266)
      | ~ m1_orders_2('#skF_5','#skF_3',B_266)
      | B_266 = '#skF_5'
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1048])).

tff(c_1850,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_1840])).

tff(c_1859,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1850])).

tff(c_1860,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1859])).

tff(c_14,plain,(
    ! [A_11] :
      ( m1_orders_2(k1_xboole_0,A_11,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1011,plain,
    ( m1_orders_2(k1_xboole_0,'#skF_3',k1_xboole_0)
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1006,c_14])).

tff(c_1024,plain,
    ( m1_orders_2(k1_xboole_0,'#skF_3',k1_xboole_0)
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1011])).

tff(c_1025,plain,(
    m1_orders_2(k1_xboole_0,'#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1024])).

tff(c_1732,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1729,c_1025])).

tff(c_1864,plain,(
    m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1860,c_1860,c_1732])).

tff(c_1876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_1864])).

tff(c_1877,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_1905,plain,(
    ! [B_271] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),B_271)
      | ~ r1_tarski('#skF_4',B_271) ) ),
    inference(resolution,[status(thm)],[c_1877,c_2])).

tff(c_1931,plain,(
    ! [B_273,B_274] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),B_273)
      | ~ r1_tarski(B_274,B_273)
      | ~ r1_tarski('#skF_4',B_274) ) ),
    inference(resolution,[status(thm)],[c_1905,c_76])).

tff(c_1945,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_1931])).

tff(c_1954,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1945])).

tff(c_1878,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_20,plain,(
    ! [A_11,B_23,C_29] :
      ( k3_orders_2(A_11,B_23,'#skF_2'(A_11,B_23,C_29)) = C_29
      | ~ m1_orders_2(C_29,A_11,B_23)
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1989,plain,(
    ! [A_277,B_278,C_279] :
      ( k3_orders_2(A_277,B_278,'#skF_2'(A_277,B_278,C_279)) = C_279
      | ~ m1_orders_2(C_279,A_277,B_278)
      | B_278 = '#skF_5'
      | ~ m1_subset_1(C_279,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_orders_2(A_277)
      | ~ v5_orders_2(A_277)
      | ~ v4_orders_2(A_277)
      | ~ v3_orders_2(A_277)
      | v2_struct_0(A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_20])).

tff(c_1994,plain,(
    ! [B_278] :
      ( k3_orders_2('#skF_3',B_278,'#skF_2'('#skF_3',B_278,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_278)
      | B_278 = '#skF_5'
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_1989])).

tff(c_2006,plain,(
    ! [B_278] :
      ( k3_orders_2('#skF_3',B_278,'#skF_2'('#skF_3',B_278,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_278)
      | B_278 = '#skF_5'
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1994])).

tff(c_2073,plain,(
    ! [B_284] :
      ( k3_orders_2('#skF_3',B_284,'#skF_2'('#skF_3',B_284,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_284)
      | B_284 = '#skF_5'
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2006])).

tff(c_2086,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_2073])).

tff(c_2096,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2086])).

tff(c_2097,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1878,c_2096])).

tff(c_2102,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2097,c_30])).

tff(c_2109,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1954,c_38,c_2102])).

tff(c_2112,plain,(
    ! [B_285] :
      ( r2_hidden(B_285,'#skF_4')
      | ~ r2_hidden(B_285,'#skF_5')
      | ~ m1_subset_1(B_285,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2109])).

tff(c_2154,plain,(
    ! [A_286] :
      ( r2_hidden(A_286,'#skF_4')
      | ~ r2_hidden(A_286,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_149,c_2112])).

tff(c_2182,plain,(
    ! [B_287] :
      ( r2_hidden('#skF_1'('#skF_5',B_287),'#skF_4')
      | r1_tarski('#skF_5',B_287) ) ),
    inference(resolution,[status(thm)],[c_6,c_2154])).

tff(c_2190,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2182,c_4])).

tff(c_2196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_2190])).

tff(c_2198,plain,(
    m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_2236,plain,(
    ! [B_293] :
      ( r2_hidden('#skF_2'('#skF_3',B_293,'#skF_5'),B_293)
      | ~ m1_orders_2('#skF_5','#skF_3',B_293)
      | B_293 = '#skF_5'
      | ~ m1_subset_1(B_293,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1048])).

tff(c_2249,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_2236])).

tff(c_2259,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2249])).

tff(c_2260,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2259])).

tff(c_1005,plain,
    ( ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_1067,plain,(
    ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1005])).

tff(c_1752,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1067])).

tff(c_2264,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2260,c_1752])).

tff(c_2277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_2264])).

tff(c_2278,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2259])).

tff(c_2325,plain,(
    ! [B_299] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),B_299)
      | ~ r1_tarski('#skF_4',B_299) ) ),
    inference(resolution,[status(thm)],[c_2278,c_2])).

tff(c_2360,plain,(
    ! [B_302,B_303] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),B_302)
      | ~ r1_tarski(B_303,B_302)
      | ~ r1_tarski('#skF_4',B_303) ) ),
    inference(resolution,[status(thm)],[c_2325,c_2])).

tff(c_2376,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_2360])).

tff(c_2386,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2376])).

tff(c_2424,plain,(
    ! [B_307] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),B_307)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_307) ) ),
    inference(resolution,[status(thm)],[c_2386,c_76])).

tff(c_2439,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_65,c_2424])).

tff(c_2279,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2259])).

tff(c_2395,plain,(
    ! [A_304,B_305,C_306] :
      ( k3_orders_2(A_304,B_305,'#skF_2'(A_304,B_305,C_306)) = C_306
      | ~ m1_orders_2(C_306,A_304,B_305)
      | B_305 = '#skF_5'
      | ~ m1_subset_1(C_306,k1_zfmisc_1(u1_struct_0(A_304)))
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0(A_304)))
      | ~ l1_orders_2(A_304)
      | ~ v5_orders_2(A_304)
      | ~ v4_orders_2(A_304)
      | ~ v3_orders_2(A_304)
      | v2_struct_0(A_304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_20])).

tff(c_2403,plain,(
    ! [B_305] :
      ( k3_orders_2('#skF_3',B_305,'#skF_2'('#skF_3',B_305,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_305)
      | B_305 = '#skF_5'
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_143,c_2395])).

tff(c_2416,plain,(
    ! [B_305] :
      ( k3_orders_2('#skF_3',B_305,'#skF_2'('#skF_3',B_305,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_305)
      | B_305 = '#skF_5'
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_2403])).

tff(c_2615,plain,(
    ! [B_320] :
      ( k3_orders_2('#skF_3',B_320,'#skF_2'('#skF_3',B_320,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_320)
      | B_320 = '#skF_5'
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2416])).

tff(c_2631,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_2615])).

tff(c_2642,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2631])).

tff(c_2643,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2279,c_2642])).

tff(c_2654,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2643,c_30])).

tff(c_2661,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(B_45,'#skF_5')
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_2439,c_38,c_2654])).

tff(c_2719,plain,(
    ! [B_326] :
      ( r2_hidden(B_326,'#skF_4')
      | ~ r2_hidden(B_326,'#skF_5')
      | ~ m1_subset_1(B_326,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2661])).

tff(c_2773,plain,(
    ! [A_327] :
      ( r2_hidden(A_327,'#skF_4')
      | ~ r2_hidden(A_327,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_149,c_2719])).

tff(c_2808,plain,(
    ! [B_328] :
      ( r2_hidden('#skF_1'('#skF_5',B_328),'#skF_4')
      | r1_tarski('#skF_5',B_328) ) ),
    inference(resolution,[status(thm)],[c_6,c_2773])).

tff(c_2816,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2808,c_4])).

tff(c_2822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_2816])).

tff(c_2823,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1005])).

tff(c_2826,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_215])).

tff(c_2827,plain,(
    ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2826])).

tff(c_2849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2823,c_2827])).

tff(c_2850,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2826])).

tff(c_2873,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2823,c_2850])).

tff(c_2881,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2873,c_34])).

tff(c_2886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:30:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.00  
% 5.31/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.00  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.31/2.00  
% 5.31/2.00  %Foreground sorts:
% 5.31/2.00  
% 5.31/2.00  
% 5.31/2.00  %Background operators:
% 5.31/2.00  
% 5.31/2.00  
% 5.31/2.00  %Foreground operators:
% 5.31/2.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.31/2.00  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.31/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.31/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.31/2.00  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 5.31/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.31/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.31/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.31/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.31/2.00  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.31/2.00  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.31/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.31/2.00  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.31/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/2.00  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 5.31/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.31/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/2.00  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.31/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.31/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.31/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.31/2.00  
% 5.31/2.03  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.31/2.03  tff(f_141, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 5.31/2.03  tff(f_95, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_orders_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 5.31/2.03  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.31/2.03  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.31/2.03  tff(f_77, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 5.31/2.03  tff(f_121, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 5.31/2.03  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/2.03  tff(c_60, plain, (![A_62, B_63]: (~r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/2.03  tff(c_65, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_60])).
% 5.31/2.03  tff(c_34, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_46, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_44, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_42, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_40, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_36, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.31/2.03  tff(c_137, plain, (![C_92, A_93, B_94]: (m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_orders_2(C_92, A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.31/2.03  tff(c_139, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_137])).
% 5.31/2.03  tff(c_142, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_139])).
% 5.31/2.03  tff(c_143, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_142])).
% 5.31/2.03  tff(c_12, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.31/2.03  tff(c_149, plain, (![A_8]: (m1_subset_1(A_8, u1_struct_0('#skF_3')) | ~r2_hidden(A_8, '#skF_5'))), inference(resolution, [status(thm)], [c_143, c_12])).
% 5.31/2.03  tff(c_49, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.31/2.03  tff(c_53, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_49])).
% 5.31/2.03  tff(c_1028, plain, (![A_186, B_187, C_188]: (r2_hidden('#skF_2'(A_186, B_187, C_188), B_187) | ~m1_orders_2(C_188, A_186, B_187) | k1_xboole_0=B_187 | ~m1_subset_1(C_188, k1_zfmisc_1(u1_struct_0(A_186))) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_orders_2(A_186) | ~v5_orders_2(A_186) | ~v4_orders_2(A_186) | ~v3_orders_2(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.03  tff(c_1032, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_5'), B_187) | ~m1_orders_2('#skF_5', '#skF_3', B_187) | k1_xboole_0=B_187 | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_143, c_1028])).
% 5.31/2.03  tff(c_1047, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_5'), B_187) | ~m1_orders_2('#skF_5', '#skF_3', B_187) | k1_xboole_0=B_187 | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1032])).
% 5.31/2.03  tff(c_1246, plain, (![B_221]: (r2_hidden('#skF_2'('#skF_3', B_221, '#skF_5'), B_221) | ~m1_orders_2('#skF_5', '#skF_3', B_221) | k1_xboole_0=B_221 | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_1047])).
% 5.31/2.03  tff(c_1258, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_1246])).
% 5.31/2.03  tff(c_1265, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1258])).
% 5.31/2.03  tff(c_1266, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1265])).
% 5.31/2.03  tff(c_277, plain, (![A_121, B_122, C_123]: (r2_hidden('#skF_2'(A_121, B_122, C_123), B_122) | ~m1_orders_2(C_123, A_121, B_122) | k1_xboole_0=B_122 | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_121))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.03  tff(c_279, plain, (![B_122]: (r2_hidden('#skF_2'('#skF_3', B_122, '#skF_5'), B_122) | ~m1_orders_2('#skF_5', '#skF_3', B_122) | k1_xboole_0=B_122 | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_143, c_277])).
% 5.31/2.03  tff(c_290, plain, (![B_122]: (r2_hidden('#skF_2'('#skF_3', B_122, '#skF_5'), B_122) | ~m1_orders_2('#skF_5', '#skF_3', B_122) | k1_xboole_0=B_122 | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_279])).
% 5.31/2.03  tff(c_394, plain, (![B_140]: (r2_hidden('#skF_2'('#skF_3', B_140, '#skF_5'), B_140) | ~m1_orders_2('#skF_5', '#skF_3', B_140) | k1_xboole_0=B_140 | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_290])).
% 5.31/2.03  tff(c_404, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_394])).
% 5.31/2.03  tff(c_410, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_404])).
% 5.31/2.03  tff(c_411, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_410])).
% 5.31/2.03  tff(c_67, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/2.03  tff(c_83, plain, (![A_75, B_76, B_77]: (r2_hidden('#skF_1'(A_75, B_76), B_77) | ~r1_tarski(A_75, B_77) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_6, c_67])).
% 5.31/2.03  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/2.03  tff(c_111, plain, (![A_85, B_86, B_87, B_88]: (r2_hidden('#skF_1'(A_85, B_86), B_87) | ~r1_tarski(B_88, B_87) | ~r1_tarski(A_85, B_88) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_83, c_2])).
% 5.31/2.03  tff(c_121, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), u1_struct_0('#skF_3')) | ~r1_tarski(A_89, '#skF_4') | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_53, c_111])).
% 5.31/2.03  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/2.03  tff(c_132, plain, (![A_89]: (~r1_tarski(A_89, '#skF_4') | r1_tarski(A_89, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_121, c_4])).
% 5.31/2.03  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.31/2.03  tff(c_201, plain, (![C_111, A_112]: (k1_xboole_0=C_111 | ~m1_orders_2(C_111, A_112, k1_xboole_0) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.03  tff(c_211, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_201])).
% 5.31/2.03  tff(c_220, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_211])).
% 5.31/2.03  tff(c_221, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_220])).
% 5.31/2.03  tff(c_222, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_221])).
% 5.31/2.03  tff(c_226, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_222])).
% 5.31/2.03  tff(c_234, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_132, c_226])).
% 5.31/2.03  tff(c_415, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_234])).
% 5.31/2.03  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_415])).
% 5.31/2.03  tff(c_424, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_410])).
% 5.31/2.03  tff(c_475, plain, (![B_146]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_146) | ~r1_tarski('#skF_4', B_146))), inference(resolution, [status(thm)], [c_424, c_2])).
% 5.31/2.03  tff(c_71, plain, (![A_68, C_69, B_70]: (m1_subset_1(A_68, C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.31/2.03  tff(c_76, plain, (![A_68, B_7, A_6]: (m1_subset_1(A_68, B_7) | ~r2_hidden(A_68, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_71])).
% 5.31/2.03  tff(c_524, plain, (![B_149, B_150]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_149) | ~r1_tarski(B_150, B_149) | ~r1_tarski('#skF_4', B_150))), inference(resolution, [status(thm)], [c_475, c_76])).
% 5.31/2.03  tff(c_538, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_53, c_524])).
% 5.31/2.03  tff(c_547, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_538])).
% 5.31/2.03  tff(c_425, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_410])).
% 5.31/2.03  tff(c_674, plain, (![A_161, B_162, C_163]: (k3_orders_2(A_161, B_162, '#skF_2'(A_161, B_162, C_163))=C_163 | ~m1_orders_2(C_163, A_161, B_162) | k1_xboole_0=B_162 | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(A_161))) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_orders_2(A_161) | ~v5_orders_2(A_161) | ~v4_orders_2(A_161) | ~v3_orders_2(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.03  tff(c_679, plain, (![B_162]: (k3_orders_2('#skF_3', B_162, '#skF_2'('#skF_3', B_162, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_162) | k1_xboole_0=B_162 | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_143, c_674])).
% 5.31/2.03  tff(c_691, plain, (![B_162]: (k3_orders_2('#skF_3', B_162, '#skF_2'('#skF_3', B_162, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_162) | k1_xboole_0=B_162 | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_679])).
% 5.31/2.03  tff(c_865, plain, (![B_182]: (k3_orders_2('#skF_3', B_182, '#skF_2'('#skF_3', B_182, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_182) | k1_xboole_0=B_182 | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_691])).
% 5.31/2.03  tff(c_878, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_865])).
% 5.31/2.03  tff(c_885, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_878])).
% 5.31/2.03  tff(c_886, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_425, c_885])).
% 5.31/2.03  tff(c_30, plain, (![B_45, D_51, A_37, C_49]: (r2_hidden(B_45, D_51) | ~r2_hidden(B_45, k3_orders_2(A_37, D_51, C_49)) | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(C_49, u1_struct_0(A_37)) | ~m1_subset_1(B_45, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | ~v5_orders_2(A_37) | ~v4_orders_2(A_37) | ~v3_orders_2(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.31/2.03  tff(c_891, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_886, c_30])).
% 5.31/2.03  tff(c_898, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_547, c_38, c_891])).
% 5.31/2.03  tff(c_901, plain, (![B_183]: (r2_hidden(B_183, '#skF_4') | ~r2_hidden(B_183, '#skF_5') | ~m1_subset_1(B_183, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_898])).
% 5.31/2.03  tff(c_943, plain, (![A_184]: (r2_hidden(A_184, '#skF_4') | ~r2_hidden(A_184, '#skF_5'))), inference(resolution, [status(thm)], [c_149, c_901])).
% 5.31/2.03  tff(c_990, plain, (![B_185]: (r2_hidden('#skF_1'('#skF_5', B_185), '#skF_4') | r1_tarski('#skF_5', B_185))), inference(resolution, [status(thm)], [c_6, c_943])).
% 5.31/2.03  tff(c_998, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_990, c_4])).
% 5.31/2.03  tff(c_1004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_998])).
% 5.31/2.03  tff(c_1006, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_221])).
% 5.31/2.03  tff(c_203, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_143, c_201])).
% 5.31/2.03  tff(c_214, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_203])).
% 5.31/2.03  tff(c_215, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_214])).
% 5.31/2.03  tff(c_1069, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_215])).
% 5.31/2.03  tff(c_1070, plain, (~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1069])).
% 5.31/2.03  tff(c_1274, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1070])).
% 5.31/2.03  tff(c_1284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1274])).
% 5.31/2.03  tff(c_1285, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1265])).
% 5.31/2.03  tff(c_1320, plain, (![B_226]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_226) | ~r1_tarski('#skF_4', B_226))), inference(resolution, [status(thm)], [c_1285, c_2])).
% 5.31/2.03  tff(c_1424, plain, (![B_234, B_235]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_234) | ~r1_tarski(B_235, B_234) | ~r1_tarski('#skF_4', B_235))), inference(resolution, [status(thm)], [c_1320, c_76])).
% 5.31/2.03  tff(c_1442, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_53, c_1424])).
% 5.31/2.03  tff(c_1453, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1442])).
% 5.31/2.03  tff(c_1286, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1265])).
% 5.31/2.03  tff(c_1393, plain, (![A_231, B_232, C_233]: (k3_orders_2(A_231, B_232, '#skF_2'(A_231, B_232, C_233))=C_233 | ~m1_orders_2(C_233, A_231, B_232) | k1_xboole_0=B_232 | ~m1_subset_1(C_233, k1_zfmisc_1(u1_struct_0(A_231))) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_orders_2(A_231) | ~v5_orders_2(A_231) | ~v4_orders_2(A_231) | ~v3_orders_2(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.03  tff(c_1400, plain, (![B_232]: (k3_orders_2('#skF_3', B_232, '#skF_2'('#skF_3', B_232, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_232) | k1_xboole_0=B_232 | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_143, c_1393])).
% 5.31/2.03  tff(c_1416, plain, (![B_232]: (k3_orders_2('#skF_3', B_232, '#skF_2'('#skF_3', B_232, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_232) | k1_xboole_0=B_232 | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1400])).
% 5.31/2.03  tff(c_1592, plain, (![B_245]: (k3_orders_2('#skF_3', B_245, '#skF_2'('#skF_3', B_245, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_245) | k1_xboole_0=B_245 | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_1416])).
% 5.31/2.03  tff(c_1607, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_1592])).
% 5.31/2.03  tff(c_1615, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1607])).
% 5.31/2.03  tff(c_1616, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1286, c_1615])).
% 5.31/2.03  tff(c_1621, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1616, c_30])).
% 5.31/2.03  tff(c_1628, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1453, c_38, c_1621])).
% 5.31/2.03  tff(c_1631, plain, (![B_246]: (r2_hidden(B_246, '#skF_4') | ~r2_hidden(B_246, '#skF_5') | ~m1_subset_1(B_246, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_1628])).
% 5.31/2.03  tff(c_1681, plain, (![A_247]: (r2_hidden(A_247, '#skF_4') | ~r2_hidden(A_247, '#skF_5'))), inference(resolution, [status(thm)], [c_149, c_1631])).
% 5.31/2.03  tff(c_1714, plain, (![B_248]: (r2_hidden('#skF_1'('#skF_5', B_248), '#skF_4') | r1_tarski('#skF_5', B_248))), inference(resolution, [status(thm)], [c_6, c_1681])).
% 5.31/2.03  tff(c_1722, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1714, c_4])).
% 5.31/2.03  tff(c_1728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_1722])).
% 5.31/2.03  tff(c_1729, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1069])).
% 5.31/2.03  tff(c_1040, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_4'), B_187) | ~m1_orders_2('#skF_4', '#skF_3', B_187) | k1_xboole_0=B_187 | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_1028])).
% 5.31/2.03  tff(c_1053, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_4'), B_187) | ~m1_orders_2('#skF_4', '#skF_3', B_187) | k1_xboole_0=B_187 | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1040])).
% 5.31/2.03  tff(c_1054, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_4'), B_187) | ~m1_orders_2('#skF_4', '#skF_3', B_187) | k1_xboole_0=B_187 | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_1053])).
% 5.31/2.03  tff(c_1761, plain, (![B_253]: (r2_hidden('#skF_2'('#skF_3', B_253, '#skF_4'), B_253) | ~m1_orders_2('#skF_4', '#skF_3', B_253) | B_253='#skF_5' | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1054])).
% 5.31/2.03  tff(c_1775, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_4'), '#skF_4') | ~m1_orders_2('#skF_4', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_1761])).
% 5.31/2.03  tff(c_1778, plain, (~m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1775])).
% 5.31/2.03  tff(c_1048, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_3', B_187, '#skF_5'), B_187) | ~m1_orders_2('#skF_5', '#skF_3', B_187) | k1_xboole_0=B_187 | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_1047])).
% 5.31/2.03  tff(c_1840, plain, (![B_266]: (r2_hidden('#skF_2'('#skF_3', B_266, '#skF_5'), B_266) | ~m1_orders_2('#skF_5', '#skF_3', B_266) | B_266='#skF_5' | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1048])).
% 5.31/2.03  tff(c_1850, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_1840])).
% 5.31/2.03  tff(c_1859, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1850])).
% 5.31/2.03  tff(c_1860, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1859])).
% 5.31/2.03  tff(c_14, plain, (![A_11]: (m1_orders_2(k1_xboole_0, A_11, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.03  tff(c_1011, plain, (m1_orders_2(k1_xboole_0, '#skF_3', k1_xboole_0) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1006, c_14])).
% 5.31/2.03  tff(c_1024, plain, (m1_orders_2(k1_xboole_0, '#skF_3', k1_xboole_0) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1011])).
% 5.31/2.03  tff(c_1025, plain, (m1_orders_2(k1_xboole_0, '#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_1024])).
% 5.31/2.03  tff(c_1732, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1729, c_1025])).
% 5.31/2.03  tff(c_1864, plain, (m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1860, c_1860, c_1732])).
% 5.31/2.03  tff(c_1876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1778, c_1864])).
% 5.31/2.03  tff(c_1877, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1859])).
% 5.31/2.03  tff(c_1905, plain, (![B_271]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_271) | ~r1_tarski('#skF_4', B_271))), inference(resolution, [status(thm)], [c_1877, c_2])).
% 5.31/2.03  tff(c_1931, plain, (![B_273, B_274]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_273) | ~r1_tarski(B_274, B_273) | ~r1_tarski('#skF_4', B_274))), inference(resolution, [status(thm)], [c_1905, c_76])).
% 5.31/2.03  tff(c_1945, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_53, c_1931])).
% 5.31/2.03  tff(c_1954, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1945])).
% 5.31/2.03  tff(c_1878, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_1859])).
% 5.31/2.03  tff(c_20, plain, (![A_11, B_23, C_29]: (k3_orders_2(A_11, B_23, '#skF_2'(A_11, B_23, C_29))=C_29 | ~m1_orders_2(C_29, A_11, B_23) | k1_xboole_0=B_23 | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.31/2.03  tff(c_1989, plain, (![A_277, B_278, C_279]: (k3_orders_2(A_277, B_278, '#skF_2'(A_277, B_278, C_279))=C_279 | ~m1_orders_2(C_279, A_277, B_278) | B_278='#skF_5' | ~m1_subset_1(C_279, k1_zfmisc_1(u1_struct_0(A_277))) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_orders_2(A_277) | ~v5_orders_2(A_277) | ~v4_orders_2(A_277) | ~v3_orders_2(A_277) | v2_struct_0(A_277))), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_20])).
% 5.31/2.03  tff(c_1994, plain, (![B_278]: (k3_orders_2('#skF_3', B_278, '#skF_2'('#skF_3', B_278, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_278) | B_278='#skF_5' | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_143, c_1989])).
% 5.31/2.03  tff(c_2006, plain, (![B_278]: (k3_orders_2('#skF_3', B_278, '#skF_2'('#skF_3', B_278, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_278) | B_278='#skF_5' | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1994])).
% 5.31/2.03  tff(c_2073, plain, (![B_284]: (k3_orders_2('#skF_3', B_284, '#skF_2'('#skF_3', B_284, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_284) | B_284='#skF_5' | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_2006])).
% 5.31/2.03  tff(c_2086, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_2073])).
% 5.31/2.03  tff(c_2096, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2086])).
% 5.31/2.03  tff(c_2097, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1878, c_2096])).
% 5.31/2.03  tff(c_2102, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2097, c_30])).
% 5.31/2.03  tff(c_2109, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1954, c_38, c_2102])).
% 5.31/2.03  tff(c_2112, plain, (![B_285]: (r2_hidden(B_285, '#skF_4') | ~r2_hidden(B_285, '#skF_5') | ~m1_subset_1(B_285, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_2109])).
% 5.31/2.03  tff(c_2154, plain, (![A_286]: (r2_hidden(A_286, '#skF_4') | ~r2_hidden(A_286, '#skF_5'))), inference(resolution, [status(thm)], [c_149, c_2112])).
% 5.31/2.03  tff(c_2182, plain, (![B_287]: (r2_hidden('#skF_1'('#skF_5', B_287), '#skF_4') | r1_tarski('#skF_5', B_287))), inference(resolution, [status(thm)], [c_6, c_2154])).
% 5.31/2.03  tff(c_2190, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2182, c_4])).
% 5.31/2.03  tff(c_2196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_2190])).
% 5.31/2.03  tff(c_2198, plain, (m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1775])).
% 5.31/2.03  tff(c_2236, plain, (![B_293]: (r2_hidden('#skF_2'('#skF_3', B_293, '#skF_5'), B_293) | ~m1_orders_2('#skF_5', '#skF_3', B_293) | B_293='#skF_5' | ~m1_subset_1(B_293, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1048])).
% 5.31/2.03  tff(c_2249, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_2236])).
% 5.31/2.03  tff(c_2259, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2249])).
% 5.31/2.03  tff(c_2260, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_2259])).
% 5.31/2.03  tff(c_1005, plain, (~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_221])).
% 5.31/2.03  tff(c_1067, plain, (~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1005])).
% 5.31/2.03  tff(c_1752, plain, (~m1_orders_2('#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1067])).
% 5.31/2.03  tff(c_2264, plain, (~m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2260, c_1752])).
% 5.31/2.03  tff(c_2277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2198, c_2264])).
% 5.31/2.03  tff(c_2278, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_2259])).
% 5.31/2.03  tff(c_2325, plain, (![B_299]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_299) | ~r1_tarski('#skF_4', B_299))), inference(resolution, [status(thm)], [c_2278, c_2])).
% 5.31/2.03  tff(c_2360, plain, (![B_302, B_303]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_302) | ~r1_tarski(B_303, B_302) | ~r1_tarski('#skF_4', B_303))), inference(resolution, [status(thm)], [c_2325, c_2])).
% 5.31/2.03  tff(c_2376, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_53, c_2360])).
% 5.31/2.03  tff(c_2386, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_2376])).
% 5.31/2.03  tff(c_2424, plain, (![B_307]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), B_307) | ~r1_tarski(u1_struct_0('#skF_3'), B_307))), inference(resolution, [status(thm)], [c_2386, c_76])).
% 5.31/2.03  tff(c_2439, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_65, c_2424])).
% 5.31/2.03  tff(c_2279, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_2259])).
% 5.31/2.03  tff(c_2395, plain, (![A_304, B_305, C_306]: (k3_orders_2(A_304, B_305, '#skF_2'(A_304, B_305, C_306))=C_306 | ~m1_orders_2(C_306, A_304, B_305) | B_305='#skF_5' | ~m1_subset_1(C_306, k1_zfmisc_1(u1_struct_0(A_304))) | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0(A_304))) | ~l1_orders_2(A_304) | ~v5_orders_2(A_304) | ~v4_orders_2(A_304) | ~v3_orders_2(A_304) | v2_struct_0(A_304))), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_20])).
% 5.31/2.03  tff(c_2403, plain, (![B_305]: (k3_orders_2('#skF_3', B_305, '#skF_2'('#skF_3', B_305, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_305) | B_305='#skF_5' | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_143, c_2395])).
% 5.31/2.03  tff(c_2416, plain, (![B_305]: (k3_orders_2('#skF_3', B_305, '#skF_2'('#skF_3', B_305, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_305) | B_305='#skF_5' | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_2403])).
% 5.31/2.03  tff(c_2615, plain, (![B_320]: (k3_orders_2('#skF_3', B_320, '#skF_2'('#skF_3', B_320, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_320) | B_320='#skF_5' | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_2416])).
% 5.31/2.03  tff(c_2631, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_2615])).
% 5.31/2.03  tff(c_2642, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2631])).
% 5.31/2.03  tff(c_2643, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2279, c_2642])).
% 5.31/2.03  tff(c_2654, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2643, c_30])).
% 5.31/2.03  tff(c_2661, plain, (![B_45]: (r2_hidden(B_45, '#skF_4') | ~r2_hidden(B_45, '#skF_5') | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_2439, c_38, c_2654])).
% 5.31/2.03  tff(c_2719, plain, (![B_326]: (r2_hidden(B_326, '#skF_4') | ~r2_hidden(B_326, '#skF_5') | ~m1_subset_1(B_326, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_2661])).
% 5.31/2.03  tff(c_2773, plain, (![A_327]: (r2_hidden(A_327, '#skF_4') | ~r2_hidden(A_327, '#skF_5'))), inference(resolution, [status(thm)], [c_149, c_2719])).
% 5.31/2.03  tff(c_2808, plain, (![B_328]: (r2_hidden('#skF_1'('#skF_5', B_328), '#skF_4') | r1_tarski('#skF_5', B_328))), inference(resolution, [status(thm)], [c_6, c_2773])).
% 5.31/2.03  tff(c_2816, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2808, c_4])).
% 5.31/2.03  tff(c_2822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_2816])).
% 5.31/2.03  tff(c_2823, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1005])).
% 5.31/2.03  tff(c_2826, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_215])).
% 5.31/2.03  tff(c_2827, plain, (~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2826])).
% 5.31/2.03  tff(c_2849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2823, c_2827])).
% 5.31/2.03  tff(c_2850, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2826])).
% 5.31/2.03  tff(c_2873, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2823, c_2850])).
% 5.31/2.03  tff(c_2881, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2873, c_34])).
% 5.31/2.03  tff(c_2886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_2881])).
% 5.31/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.03  
% 5.31/2.03  Inference rules
% 5.31/2.03  ----------------------
% 5.31/2.03  #Ref     : 0
% 5.31/2.03  #Sup     : 630
% 5.31/2.03  #Fact    : 0
% 5.31/2.03  #Define  : 0
% 5.31/2.03  #Split   : 21
% 5.31/2.03  #Chain   : 0
% 5.31/2.03  #Close   : 0
% 5.31/2.03  
% 5.31/2.03  Ordering : KBO
% 5.31/2.03  
% 5.31/2.03  Simplification rules
% 5.31/2.03  ----------------------
% 5.31/2.03  #Subsume      : 116
% 5.31/2.03  #Demod        : 465
% 5.31/2.03  #Tautology    : 104
% 5.31/2.03  #SimpNegUnit  : 59
% 5.31/2.03  #BackRed      : 77
% 5.31/2.03  
% 5.31/2.03  #Partial instantiations: 0
% 5.31/2.03  #Strategies tried      : 1
% 5.31/2.03  
% 5.31/2.03  Timing (in seconds)
% 5.31/2.03  ----------------------
% 5.31/2.04  Preprocessing        : 0.31
% 5.31/2.04  Parsing              : 0.16
% 5.31/2.04  CNF conversion       : 0.03
% 5.31/2.04  Main loop            : 0.90
% 5.31/2.04  Inferencing          : 0.27
% 5.31/2.04  Reduction            : 0.28
% 5.31/2.04  Demodulation         : 0.18
% 5.31/2.04  BG Simplification    : 0.04
% 5.31/2.04  Subsumption          : 0.25
% 5.31/2.04  Abstraction          : 0.04
% 5.31/2.04  MUC search           : 0.00
% 5.31/2.04  Cooper               : 0.00
% 5.31/2.04  Total                : 1.27
% 5.31/2.04  Index Insertion      : 0.00
% 5.31/2.04  Index Deletion       : 0.00
% 5.31/2.04  Index Matching       : 0.00
% 5.31/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
