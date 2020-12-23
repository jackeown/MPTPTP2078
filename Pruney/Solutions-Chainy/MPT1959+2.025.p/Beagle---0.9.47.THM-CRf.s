%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:00 EST 2020

% Result     : Theorem 12.85s
% Output     : CNFRefutation 12.85s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 499 expanded)
%              Number of leaves         :   49 ( 190 expanded)
%              Depth                    :   26
%              Number of atoms          :  417 (1771 expanded)
%              Number of equality atoms :   34 (  73 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k5_waybel_0(A,B))
            & k1_yellow_0(A,k5_waybel_0(A,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_18,plain,(
    ! [A_12] : ~ v1_subset_1('#skF_4'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1('#skF_4'(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_269,plain,(
    ! [B_111,A_112] :
      ( v1_subset_1(B_111,A_112)
      | B_111 = A_112
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_272,plain,(
    ! [A_12] :
      ( v1_subset_1('#skF_4'(A_12),A_12)
      | '#skF_4'(A_12) = A_12 ) ),
    inference(resolution,[status(thm)],[c_20,c_269])).

tff(c_284,plain,(
    ! [A_12] : '#skF_4'(A_12) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_272])).

tff(c_290,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_18])).

tff(c_289,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_20])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_74,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_70,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_66,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1('#skF_3'(A_8,B_9),A_8)
      | B_9 = A_8
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20848,plain,(
    ! [A_933,B_934] :
      ( k1_yellow_0(A_933,k5_waybel_0(A_933,B_934)) = B_934
      | ~ m1_subset_1(B_934,u1_struct_0(A_933))
      | ~ l1_orders_2(A_933)
      | ~ v5_orders_2(A_933)
      | ~ v4_orders_2(A_933)
      | ~ v3_orders_2(A_933)
      | v2_struct_0(A_933) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_23725,plain,(
    ! [A_1063,B_1064] :
      ( k1_yellow_0(A_1063,k5_waybel_0(A_1063,'#skF_3'(u1_struct_0(A_1063),B_1064))) = '#skF_3'(u1_struct_0(A_1063),B_1064)
      | ~ l1_orders_2(A_1063)
      | ~ v5_orders_2(A_1063)
      | ~ v4_orders_2(A_1063)
      | ~ v3_orders_2(A_1063)
      | v2_struct_0(A_1063)
      | u1_struct_0(A_1063) = B_1064
      | ~ m1_subset_1(B_1064,k1_zfmisc_1(u1_struct_0(A_1063))) ) ),
    inference(resolution,[status(thm)],[c_14,c_20848])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k1_yellow_0(A_23,B_24),u1_struct_0(A_23))
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_301,plain,(
    ! [C_115,B_116,A_117] :
      ( ~ v1_xboole_0(C_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(C_115))
      | ~ r2_hidden(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_310,plain,(
    ! [A_117] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_117,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_301])).

tff(c_367,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_256,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_1'(A_106,B_107),A_106)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_106] : r1_tarski(A_106,A_106) ),
    inference(resolution,[status(thm)],[c_256,c_4])).

tff(c_1799,plain,(
    ! [A_247,B_248] :
      ( k1_yellow_0(A_247,k5_waybel_0(A_247,B_248)) = B_248
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l1_orders_2(A_247)
      | ~ v5_orders_2(A_247)
      | ~ v4_orders_2(A_247)
      | ~ v3_orders_2(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1846,plain,(
    ! [A_247,B_9] :
      ( k1_yellow_0(A_247,k5_waybel_0(A_247,'#skF_3'(u1_struct_0(A_247),B_9))) = '#skF_3'(u1_struct_0(A_247),B_9)
      | ~ l1_orders_2(A_247)
      | ~ v5_orders_2(A_247)
      | ~ v4_orders_2(A_247)
      | ~ v3_orders_2(A_247)
      | v2_struct_0(A_247)
      | u1_struct_0(A_247) = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_247))) ) ),
    inference(resolution,[status(thm)],[c_14,c_1799])).

tff(c_52,plain,(
    ! [A_56,B_58] :
      ( r1_yellow_0(A_56,k5_waybel_0(A_56,B_58))
      | ~ m1_subset_1(B_58,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1858,plain,(
    ! [A_23,B_24] :
      ( k1_yellow_0(A_23,k5_waybel_0(A_23,k1_yellow_0(A_23,B_24))) = k1_yellow_0(A_23,B_24)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(resolution,[status(thm)],[c_30,c_1799])).

tff(c_60,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_107,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,B_72)
      | v1_xboole_0(B_72)
      | ~ m1_subset_1(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_105,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_107,c_105])).

tff(c_113,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_110])).

tff(c_78,plain,
    ( r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
    | ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_114,plain,(
    ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_78])).

tff(c_194,plain,(
    ! [B_95,A_96] :
      ( v1_subset_1(B_95,A_96)
      | B_95 = A_96
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_206,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_58,c_194])).

tff(c_214,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_206])).

tff(c_96,plain,(
    ! [A_68] :
      ( k1_yellow_0(A_68,k1_xboole_0) = k3_yellow_0(A_68)
      | ~ l1_orders_2(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_100,plain,(
    k1_yellow_0('#skF_7',k1_xboole_0) = k3_yellow_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_115,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k1_yellow_0(A_73,B_74),u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_115])).

tff(c_120,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_118])).

tff(c_240,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_120])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_240])).

tff(c_246,plain,(
    r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_309,plain,(
    ! [A_11,A_117] :
      ( ~ v1_xboole_0(A_11)
      | ~ r2_hidden(A_117,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_301])).

tff(c_330,plain,(
    ! [A_120] : ~ r2_hidden(A_120,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_340,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_330])).

tff(c_68,plain,(
    v1_yellow_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_36,plain,(
    ! [A_30] :
      ( r1_yellow_0(A_30,k1_xboole_0)
      | ~ l1_orders_2(A_30)
      | ~ v1_yellow_0(A_30)
      | ~ v5_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1599,plain,(
    ! [A_229,B_230,C_231] :
      ( r1_orders_2(A_229,k1_yellow_0(A_229,B_230),k1_yellow_0(A_229,C_231))
      | ~ r1_yellow_0(A_229,C_231)
      | ~ r1_yellow_0(A_229,B_230)
      | ~ r1_tarski(B_230,C_231)
      | ~ l1_orders_2(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1602,plain,(
    ! [C_231] :
      ( r1_orders_2('#skF_7',k3_yellow_0('#skF_7'),k1_yellow_0('#skF_7',C_231))
      | ~ r1_yellow_0('#skF_7',C_231)
      | ~ r1_yellow_0('#skF_7',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_231)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_1599])).

tff(c_1607,plain,(
    ! [C_231] :
      ( r1_orders_2('#skF_7',k3_yellow_0('#skF_7'),k1_yellow_0('#skF_7',C_231))
      | ~ r1_yellow_0('#skF_7',C_231)
      | ~ r1_yellow_0('#skF_7',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_340,c_1602])).

tff(c_1994,plain,(
    ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1607])).

tff(c_1997,plain,
    ( ~ l1_orders_2('#skF_7')
    | ~ v1_yellow_0('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_1994])).

tff(c_2000,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1997])).

tff(c_2002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2000])).

tff(c_2004,plain,(
    r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1607])).

tff(c_250,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k1_yellow_0(A_104,B_105),u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_253,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_250])).

tff(c_255,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_253])).

tff(c_32,plain,(
    ! [A_25,B_28,C_29] :
      ( r1_orders_2(A_25,k1_yellow_0(A_25,B_28),k1_yellow_0(A_25,C_29))
      | ~ r1_yellow_0(A_25,C_29)
      | ~ r1_yellow_0(A_25,B_28)
      | ~ r1_tarski(B_28,C_29)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2023,plain,(
    ! [D_253,B_254,A_255,C_256] :
      ( r2_hidden(D_253,B_254)
      | ~ r1_orders_2(A_255,C_256,D_253)
      | ~ r2_hidden(C_256,B_254)
      | ~ m1_subset_1(D_253,u1_struct_0(A_255))
      | ~ m1_subset_1(C_256,u1_struct_0(A_255))
      | ~ v13_waybel_0(B_254,A_255)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_orders_2(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5087,plain,(
    ! [A_413,C_414,B_415,B_416] :
      ( r2_hidden(k1_yellow_0(A_413,C_414),B_415)
      | ~ r2_hidden(k1_yellow_0(A_413,B_416),B_415)
      | ~ m1_subset_1(k1_yellow_0(A_413,C_414),u1_struct_0(A_413))
      | ~ m1_subset_1(k1_yellow_0(A_413,B_416),u1_struct_0(A_413))
      | ~ v13_waybel_0(B_415,A_413)
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ r1_yellow_0(A_413,C_414)
      | ~ r1_yellow_0(A_413,B_416)
      | ~ r1_tarski(B_416,C_414)
      | ~ l1_orders_2(A_413) ) ),
    inference(resolution,[status(thm)],[c_32,c_2023])).

tff(c_5120,plain,(
    ! [C_414,B_415] :
      ( r2_hidden(k1_yellow_0('#skF_7',C_414),B_415)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_415)
      | ~ m1_subset_1(k1_yellow_0('#skF_7',C_414),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(k1_yellow_0('#skF_7',k1_xboole_0),u1_struct_0('#skF_7'))
      | ~ v13_waybel_0(B_415,'#skF_7')
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r1_yellow_0('#skF_7',C_414)
      | ~ r1_yellow_0('#skF_7',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_414)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_5087])).

tff(c_8811,plain,(
    ! [C_583,B_584] :
      ( r2_hidden(k1_yellow_0('#skF_7',C_583),B_584)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_584)
      | ~ m1_subset_1(k1_yellow_0('#skF_7',C_583),u1_struct_0('#skF_7'))
      | ~ v13_waybel_0(B_584,'#skF_7')
      | ~ m1_subset_1(B_584,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r1_yellow_0('#skF_7',C_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_340,c_2004,c_255,c_100,c_5120])).

tff(c_8855,plain,(
    ! [B_24,B_584] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_24),B_584)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_584)
      | ~ v13_waybel_0(B_584,'#skF_7')
      | ~ m1_subset_1(B_584,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r1_yellow_0('#skF_7',B_24)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_8811])).

tff(c_15692,plain,(
    ! [B_825,B_826] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_825),B_826)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_826)
      | ~ v13_waybel_0(B_826,'#skF_7')
      | ~ m1_subset_1(B_826,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r1_yellow_0('#skF_7',B_825) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8855])).

tff(c_15736,plain,(
    ! [B_825] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_825),'#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
      | ~ v13_waybel_0('#skF_8','#skF_7')
      | ~ r1_yellow_0('#skF_7',B_825) ) ),
    inference(resolution,[status(thm)],[c_58,c_15692])).

tff(c_15759,plain,(
    ! [B_827] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_827),'#skF_8')
      | ~ r1_yellow_0('#skF_7',B_827) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_246,c_15736])).

tff(c_15819,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_24),'#skF_8')
      | ~ r1_yellow_0('#skF_7',k5_waybel_0('#skF_7',k1_yellow_0('#skF_7',B_24)))
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1858,c_15759])).

tff(c_15870,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_24),'#skF_8')
      | ~ r1_yellow_0('#skF_7',k5_waybel_0('#skF_7',k1_yellow_0('#skF_7',B_24)))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74,c_72,c_70,c_15819])).

tff(c_16105,plain,(
    ! [B_830] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_830),'#skF_8')
      | ~ r1_yellow_0('#skF_7',k5_waybel_0('#skF_7',k1_yellow_0('#skF_7',B_830))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_15870])).

tff(c_16177,plain,(
    ! [B_830] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_830),'#skF_8')
      | ~ m1_subset_1(k1_yellow_0('#skF_7',B_830),u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_16105])).

tff(c_16205,plain,(
    ! [B_830] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_830),'#skF_8')
      | ~ m1_subset_1(k1_yellow_0('#skF_7',B_830),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_16177])).

tff(c_16522,plain,(
    ! [B_834] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_834),'#skF_8')
      | ~ m1_subset_1(k1_yellow_0('#skF_7',B_834),u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16205])).

tff(c_16608,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_24),'#skF_8')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_16522])).

tff(c_16649,plain,(
    ! [B_835] : r2_hidden(k1_yellow_0('#skF_7',B_835),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16608])).

tff(c_16697,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_7'),B_9),'#skF_8')
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | u1_struct_0('#skF_7') = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1846,c_16649])).

tff(c_16741,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_7'),B_9),'#skF_8')
      | v2_struct_0('#skF_7')
      | u1_struct_0('#skF_7') = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_16697])).

tff(c_20414,plain,(
    ! [B_922] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_7'),B_922),'#skF_8')
      | u1_struct_0('#skF_7') = B_922
      | ~ m1_subset_1(B_922,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16741])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_3'(A_8,B_9),B_9)
      | B_9 = A_8
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20427,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_20414,c_12])).

tff(c_20447,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20427])).

tff(c_383,plain,(
    ! [A_135,C_136,B_137] :
      ( m1_subset_1(A_135,C_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(C_136))
      | ~ r2_hidden(A_135,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_395,plain,(
    ! [A_135] :
      ( m1_subset_1(A_135,u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_135,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_383])).

tff(c_342,plain,(
    ! [C_122,B_123,A_124] :
      ( r2_hidden(C_122,B_123)
      | ~ r2_hidden(C_122,A_124)
      | ~ r1_tarski(A_124,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_852,plain,(
    ! [A_175,B_176,B_177] :
      ( r2_hidden('#skF_1'(A_175,B_176),B_177)
      | ~ r1_tarski(A_175,B_177)
      | r1_tarski(A_175,B_176) ) ),
    inference(resolution,[status(thm)],[c_6,c_342])).

tff(c_263,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(A_109,B_110)
      | v1_xboole_0(B_110)
      | ~ m1_subset_1(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_519,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(A_152,B_153)
      | v1_xboole_0(B_153)
      | ~ m1_subset_1('#skF_1'(A_152,B_153),B_153) ) ),
    inference(resolution,[status(thm)],[c_263,c_4])).

tff(c_527,plain,(
    ! [A_152] :
      ( r1_tarski(A_152,u1_struct_0('#skF_7'))
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_152,u1_struct_0('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_395,c_519])).

tff(c_532,plain,(
    ! [A_152] :
      ( r1_tarski(A_152,u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_152,u1_struct_0('#skF_7')),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_527])).

tff(c_881,plain,(
    ! [A_175] :
      ( ~ r1_tarski(A_175,'#skF_8')
      | r1_tarski(A_175,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_852,c_532])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1086,plain,(
    ! [A_192,B_193,B_194] :
      ( r2_hidden(A_192,B_193)
      | ~ r1_tarski(B_194,B_193)
      | v1_xboole_0(B_194)
      | ~ m1_subset_1(A_192,B_194) ) ),
    inference(resolution,[status(thm)],[c_22,c_342])).

tff(c_1541,plain,(
    ! [A_227,A_228] :
      ( r2_hidden(A_227,u1_struct_0('#skF_7'))
      | v1_xboole_0(A_228)
      | ~ m1_subset_1(A_227,A_228)
      | ~ r1_tarski(A_228,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_881,c_1086])).

tff(c_1559,plain,(
    ! [A_135] :
      ( r2_hidden(A_135,u1_struct_0('#skF_7'))
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_8')
      | ~ r2_hidden(A_135,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_395,c_1541])).

tff(c_1586,plain,(
    ! [A_135] :
      ( r2_hidden(A_135,u1_struct_0('#skF_7'))
      | ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_8')
      | ~ r2_hidden(A_135,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_1559])).

tff(c_1610,plain,(
    ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1586])).

tff(c_20568,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20447,c_1610])).

tff(c_20604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_20568])).

tff(c_20606,plain,(
    r1_tarski(u1_struct_0('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1586])).

tff(c_349,plain,(
    ! [A_14,B_123,B_15] :
      ( r2_hidden(A_14,B_123)
      | ~ r1_tarski(B_15,B_123)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_342])).

tff(c_20612,plain,(
    ! [A_14] :
      ( r2_hidden(A_14,'#skF_8')
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_14,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_20606,c_349])).

tff(c_20693,plain,(
    ! [A_925] :
      ( r2_hidden(A_925,'#skF_8')
      | ~ m1_subset_1(A_925,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_20612])).

tff(c_20734,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_7',B_24),'#skF_8')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_20693])).

tff(c_20754,plain,(
    ! [B_24] : r2_hidden(k1_yellow_0('#skF_7',B_24),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_20734])).

tff(c_23790,plain,(
    ! [B_1064] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_7'),B_1064),'#skF_8')
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | u1_struct_0('#skF_7') = B_1064
      | ~ m1_subset_1(B_1064,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23725,c_20754])).

tff(c_23859,plain,(
    ! [B_1064] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_7'),B_1064),'#skF_8')
      | v2_struct_0('#skF_7')
      | u1_struct_0('#skF_7') = B_1064
      | ~ m1_subset_1(B_1064,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_23790])).

tff(c_24368,plain,(
    ! [B_1075] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_7'),B_1075),'#skF_8')
      | u1_struct_0('#skF_7') = B_1075
      | ~ m1_subset_1(B_1075,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_23859])).

tff(c_24375,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_24368,c_12])).

tff(c_24387,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24375])).

tff(c_584,plain,(
    ! [A_161] :
      ( r1_tarski(A_161,u1_struct_0('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_161,u1_struct_0('#skF_7')),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_527])).

tff(c_595,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_584])).

tff(c_1094,plain,(
    ! [A_192] :
      ( r2_hidden(A_192,u1_struct_0('#skF_7'))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_192,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_595,c_1086])).

tff(c_1120,plain,(
    ! [A_195] :
      ( r2_hidden(A_195,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_195,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1094])).

tff(c_1204,plain,(
    ! [A_202] :
      ( u1_struct_0('#skF_7') = A_202
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(A_202))
      | ~ m1_subset_1('#skF_3'(A_202,u1_struct_0('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1120,c_12])).

tff(c_1209,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_14,c_1204])).

tff(c_1210,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1209])).

tff(c_24436,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24387,c_1210])).

tff(c_24468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_24436])).

tff(c_24469,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1209])).

tff(c_245,plain,(
    v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_24490,plain,(
    v1_subset_1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24469,c_245])).

tff(c_24496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_24490])).

tff(c_24497,plain,(
    ! [A_117] : ~ r2_hidden(A_117,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_24500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24497,c_246])).

tff(c_24501,plain,(
    ! [A_11] : ~ v1_xboole_0(A_11) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_8,plain,(
    ! [A_6] : v1_xboole_0('#skF_2'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24501,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.85/5.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.85/5.69  
% 12.85/5.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.85/5.70  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5
% 12.85/5.70  
% 12.85/5.70  %Foreground sorts:
% 12.85/5.70  
% 12.85/5.70  
% 12.85/5.70  %Background operators:
% 12.85/5.70  
% 12.85/5.70  
% 12.85/5.70  %Foreground operators:
% 12.85/5.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.85/5.70  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 12.85/5.70  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 12.85/5.70  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 12.85/5.70  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.85/5.70  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.85/5.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.85/5.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.85/5.70  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 12.85/5.70  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 12.85/5.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.85/5.70  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 12.85/5.70  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 12.85/5.70  tff('#skF_7', type, '#skF_7': $i).
% 12.85/5.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.85/5.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.85/5.70  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 12.85/5.70  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 12.85/5.70  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 12.85/5.70  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 12.85/5.70  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 12.85/5.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.85/5.70  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 12.85/5.70  tff('#skF_8', type, '#skF_8': $i).
% 12.85/5.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.85/5.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.85/5.70  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 12.85/5.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.85/5.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.85/5.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.85/5.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.85/5.70  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 12.85/5.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.85/5.70  
% 12.85/5.72  tff(f_54, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 12.85/5.72  tff(f_149, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 12.85/5.72  tff(f_178, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 12.85/5.72  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 12.85/5.72  tff(f_142, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 12.85/5.72  tff(f_81, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 12.85/5.72  tff(f_73, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 12.85/5.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.85/5.72  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 12.85/5.72  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 12.85/5.72  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 12.85/5.72  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 12.85/5.72  tff(f_92, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 12.85/5.72  tff(f_124, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 12.85/5.72  tff(f_66, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 12.85/5.72  tff(f_37, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 12.85/5.72  tff(c_18, plain, (![A_12]: (~v1_subset_1('#skF_4'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.85/5.72  tff(c_20, plain, (![A_12]: (m1_subset_1('#skF_4'(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.85/5.72  tff(c_269, plain, (![B_111, A_112]: (v1_subset_1(B_111, A_112) | B_111=A_112 | ~m1_subset_1(B_111, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.85/5.72  tff(c_272, plain, (![A_12]: (v1_subset_1('#skF_4'(A_12), A_12) | '#skF_4'(A_12)=A_12)), inference(resolution, [status(thm)], [c_20, c_269])).
% 12.85/5.72  tff(c_284, plain, (![A_12]: ('#skF_4'(A_12)=A_12)), inference(negUnitSimplification, [status(thm)], [c_18, c_272])).
% 12.85/5.72  tff(c_290, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_18])).
% 12.85/5.72  tff(c_289, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_20])).
% 12.85/5.72  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_76, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_74, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_72, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_70, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_66, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1('#skF_3'(A_8, B_9), A_8) | B_9=A_8 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.85/5.72  tff(c_20848, plain, (![A_933, B_934]: (k1_yellow_0(A_933, k5_waybel_0(A_933, B_934))=B_934 | ~m1_subset_1(B_934, u1_struct_0(A_933)) | ~l1_orders_2(A_933) | ~v5_orders_2(A_933) | ~v4_orders_2(A_933) | ~v3_orders_2(A_933) | v2_struct_0(A_933))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.85/5.72  tff(c_23725, plain, (![A_1063, B_1064]: (k1_yellow_0(A_1063, k5_waybel_0(A_1063, '#skF_3'(u1_struct_0(A_1063), B_1064)))='#skF_3'(u1_struct_0(A_1063), B_1064) | ~l1_orders_2(A_1063) | ~v5_orders_2(A_1063) | ~v4_orders_2(A_1063) | ~v3_orders_2(A_1063) | v2_struct_0(A_1063) | u1_struct_0(A_1063)=B_1064 | ~m1_subset_1(B_1064, k1_zfmisc_1(u1_struct_0(A_1063))))), inference(resolution, [status(thm)], [c_14, c_20848])).
% 12.85/5.72  tff(c_30, plain, (![A_23, B_24]: (m1_subset_1(k1_yellow_0(A_23, B_24), u1_struct_0(A_23)) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.85/5.72  tff(c_301, plain, (![C_115, B_116, A_117]: (~v1_xboole_0(C_115) | ~m1_subset_1(B_116, k1_zfmisc_1(C_115)) | ~r2_hidden(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.85/5.72  tff(c_310, plain, (![A_117]: (~v1_xboole_0(u1_struct_0('#skF_7')) | ~r2_hidden(A_117, '#skF_8'))), inference(resolution, [status(thm)], [c_58, c_301])).
% 12.85/5.72  tff(c_367, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_310])).
% 12.85/5.72  tff(c_256, plain, (![A_106, B_107]: (r2_hidden('#skF_1'(A_106, B_107), A_106) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.85/5.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.85/5.72  tff(c_261, plain, (![A_106]: (r1_tarski(A_106, A_106))), inference(resolution, [status(thm)], [c_256, c_4])).
% 12.85/5.72  tff(c_1799, plain, (![A_247, B_248]: (k1_yellow_0(A_247, k5_waybel_0(A_247, B_248))=B_248 | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l1_orders_2(A_247) | ~v5_orders_2(A_247) | ~v4_orders_2(A_247) | ~v3_orders_2(A_247) | v2_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.85/5.72  tff(c_1846, plain, (![A_247, B_9]: (k1_yellow_0(A_247, k5_waybel_0(A_247, '#skF_3'(u1_struct_0(A_247), B_9)))='#skF_3'(u1_struct_0(A_247), B_9) | ~l1_orders_2(A_247) | ~v5_orders_2(A_247) | ~v4_orders_2(A_247) | ~v3_orders_2(A_247) | v2_struct_0(A_247) | u1_struct_0(A_247)=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_247))))), inference(resolution, [status(thm)], [c_14, c_1799])).
% 12.85/5.72  tff(c_52, plain, (![A_56, B_58]: (r1_yellow_0(A_56, k5_waybel_0(A_56, B_58)) | ~m1_subset_1(B_58, u1_struct_0(A_56)) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.85/5.72  tff(c_1858, plain, (![A_23, B_24]: (k1_yellow_0(A_23, k5_waybel_0(A_23, k1_yellow_0(A_23, B_24)))=k1_yellow_0(A_23, B_24) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23) | ~l1_orders_2(A_23))), inference(resolution, [status(thm)], [c_30, c_1799])).
% 12.85/5.72  tff(c_60, plain, (v13_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_64, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_107, plain, (![A_71, B_72]: (r2_hidden(A_71, B_72) | v1_xboole_0(B_72) | ~m1_subset_1(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.85/5.72  tff(c_84, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_105, plain, (~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 12.85/5.72  tff(c_110, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_107, c_105])).
% 12.85/5.72  tff(c_113, plain, (~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_110])).
% 12.85/5.72  tff(c_78, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_114, plain, (~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_105, c_78])).
% 12.85/5.72  tff(c_194, plain, (![B_95, A_96]: (v1_subset_1(B_95, A_96) | B_95=A_96 | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.85/5.72  tff(c_206, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | u1_struct_0('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_58, c_194])).
% 12.85/5.72  tff(c_214, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_114, c_206])).
% 12.85/5.72  tff(c_96, plain, (![A_68]: (k1_yellow_0(A_68, k1_xboole_0)=k3_yellow_0(A_68) | ~l1_orders_2(A_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.85/5.72  tff(c_100, plain, (k1_yellow_0('#skF_7', k1_xboole_0)=k3_yellow_0('#skF_7')), inference(resolution, [status(thm)], [c_66, c_96])).
% 12.85/5.72  tff(c_115, plain, (![A_73, B_74]: (m1_subset_1(k1_yellow_0(A_73, B_74), u1_struct_0(A_73)) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.85/5.72  tff(c_118, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_100, c_115])).
% 12.85/5.72  tff(c_120, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_118])).
% 12.85/5.72  tff(c_240, plain, (m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_120])).
% 12.85/5.72  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_240])).
% 12.85/5.72  tff(c_246, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 12.85/5.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.85/5.72  tff(c_16, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.85/5.72  tff(c_309, plain, (![A_11, A_117]: (~v1_xboole_0(A_11) | ~r2_hidden(A_117, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_301])).
% 12.85/5.72  tff(c_330, plain, (![A_120]: (~r2_hidden(A_120, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_309])).
% 12.85/5.72  tff(c_340, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_330])).
% 12.85/5.72  tff(c_68, plain, (v1_yellow_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.85/5.72  tff(c_36, plain, (![A_30]: (r1_yellow_0(A_30, k1_xboole_0) | ~l1_orders_2(A_30) | ~v1_yellow_0(A_30) | ~v5_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.85/5.72  tff(c_1599, plain, (![A_229, B_230, C_231]: (r1_orders_2(A_229, k1_yellow_0(A_229, B_230), k1_yellow_0(A_229, C_231)) | ~r1_yellow_0(A_229, C_231) | ~r1_yellow_0(A_229, B_230) | ~r1_tarski(B_230, C_231) | ~l1_orders_2(A_229))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.85/5.72  tff(c_1602, plain, (![C_231]: (r1_orders_2('#skF_7', k3_yellow_0('#skF_7'), k1_yellow_0('#skF_7', C_231)) | ~r1_yellow_0('#skF_7', C_231) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_231) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_1599])).
% 12.85/5.72  tff(c_1607, plain, (![C_231]: (r1_orders_2('#skF_7', k3_yellow_0('#skF_7'), k1_yellow_0('#skF_7', C_231)) | ~r1_yellow_0('#skF_7', C_231) | ~r1_yellow_0('#skF_7', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_340, c_1602])).
% 12.85/5.72  tff(c_1994, plain, (~r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1607])).
% 12.85/5.72  tff(c_1997, plain, (~l1_orders_2('#skF_7') | ~v1_yellow_0('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_1994])).
% 12.85/5.72  tff(c_2000, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1997])).
% 12.85/5.72  tff(c_2002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2000])).
% 12.85/5.72  tff(c_2004, plain, (r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1607])).
% 12.85/5.72  tff(c_250, plain, (![A_104, B_105]: (m1_subset_1(k1_yellow_0(A_104, B_105), u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.85/5.72  tff(c_253, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_100, c_250])).
% 12.85/5.72  tff(c_255, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_253])).
% 12.85/5.72  tff(c_32, plain, (![A_25, B_28, C_29]: (r1_orders_2(A_25, k1_yellow_0(A_25, B_28), k1_yellow_0(A_25, C_29)) | ~r1_yellow_0(A_25, C_29) | ~r1_yellow_0(A_25, B_28) | ~r1_tarski(B_28, C_29) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.85/5.72  tff(c_2023, plain, (![D_253, B_254, A_255, C_256]: (r2_hidden(D_253, B_254) | ~r1_orders_2(A_255, C_256, D_253) | ~r2_hidden(C_256, B_254) | ~m1_subset_1(D_253, u1_struct_0(A_255)) | ~m1_subset_1(C_256, u1_struct_0(A_255)) | ~v13_waybel_0(B_254, A_255) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_orders_2(A_255))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.85/5.72  tff(c_5087, plain, (![A_413, C_414, B_415, B_416]: (r2_hidden(k1_yellow_0(A_413, C_414), B_415) | ~r2_hidden(k1_yellow_0(A_413, B_416), B_415) | ~m1_subset_1(k1_yellow_0(A_413, C_414), u1_struct_0(A_413)) | ~m1_subset_1(k1_yellow_0(A_413, B_416), u1_struct_0(A_413)) | ~v13_waybel_0(B_415, A_413) | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0(A_413))) | ~r1_yellow_0(A_413, C_414) | ~r1_yellow_0(A_413, B_416) | ~r1_tarski(B_416, C_414) | ~l1_orders_2(A_413))), inference(resolution, [status(thm)], [c_32, c_2023])).
% 12.85/5.72  tff(c_5120, plain, (![C_414, B_415]: (r2_hidden(k1_yellow_0('#skF_7', C_414), B_415) | ~r2_hidden(k3_yellow_0('#skF_7'), B_415) | ~m1_subset_1(k1_yellow_0('#skF_7', C_414), u1_struct_0('#skF_7')) | ~m1_subset_1(k1_yellow_0('#skF_7', k1_xboole_0), u1_struct_0('#skF_7')) | ~v13_waybel_0(B_415, '#skF_7') | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r1_yellow_0('#skF_7', C_414) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_414) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_5087])).
% 12.85/5.72  tff(c_8811, plain, (![C_583, B_584]: (r2_hidden(k1_yellow_0('#skF_7', C_583), B_584) | ~r2_hidden(k3_yellow_0('#skF_7'), B_584) | ~m1_subset_1(k1_yellow_0('#skF_7', C_583), u1_struct_0('#skF_7')) | ~v13_waybel_0(B_584, '#skF_7') | ~m1_subset_1(B_584, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r1_yellow_0('#skF_7', C_583))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_340, c_2004, c_255, c_100, c_5120])).
% 12.85/5.72  tff(c_8855, plain, (![B_24, B_584]: (r2_hidden(k1_yellow_0('#skF_7', B_24), B_584) | ~r2_hidden(k3_yellow_0('#skF_7'), B_584) | ~v13_waybel_0(B_584, '#skF_7') | ~m1_subset_1(B_584, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r1_yellow_0('#skF_7', B_24) | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_8811])).
% 12.85/5.72  tff(c_15692, plain, (![B_825, B_826]: (r2_hidden(k1_yellow_0('#skF_7', B_825), B_826) | ~r2_hidden(k3_yellow_0('#skF_7'), B_826) | ~v13_waybel_0(B_826, '#skF_7') | ~m1_subset_1(B_826, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r1_yellow_0('#skF_7', B_825))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8855])).
% 12.85/5.72  tff(c_15736, plain, (![B_825]: (r2_hidden(k1_yellow_0('#skF_7', B_825), '#skF_8') | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v13_waybel_0('#skF_8', '#skF_7') | ~r1_yellow_0('#skF_7', B_825))), inference(resolution, [status(thm)], [c_58, c_15692])).
% 12.85/5.72  tff(c_15759, plain, (![B_827]: (r2_hidden(k1_yellow_0('#skF_7', B_827), '#skF_8') | ~r1_yellow_0('#skF_7', B_827))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_246, c_15736])).
% 12.85/5.72  tff(c_15819, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_7', B_24), '#skF_8') | ~r1_yellow_0('#skF_7', k5_waybel_0('#skF_7', k1_yellow_0('#skF_7', B_24))) | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1858, c_15759])).
% 12.85/5.72  tff(c_15870, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_7', B_24), '#skF_8') | ~r1_yellow_0('#skF_7', k5_waybel_0('#skF_7', k1_yellow_0('#skF_7', B_24))) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74, c_72, c_70, c_15819])).
% 12.85/5.72  tff(c_16105, plain, (![B_830]: (r2_hidden(k1_yellow_0('#skF_7', B_830), '#skF_8') | ~r1_yellow_0('#skF_7', k5_waybel_0('#skF_7', k1_yellow_0('#skF_7', B_830))))), inference(negUnitSimplification, [status(thm)], [c_76, c_15870])).
% 12.85/5.72  tff(c_16177, plain, (![B_830]: (r2_hidden(k1_yellow_0('#skF_7', B_830), '#skF_8') | ~m1_subset_1(k1_yellow_0('#skF_7', B_830), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_16105])).
% 12.85/5.72  tff(c_16205, plain, (![B_830]: (r2_hidden(k1_yellow_0('#skF_7', B_830), '#skF_8') | ~m1_subset_1(k1_yellow_0('#skF_7', B_830), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_66, c_16177])).
% 12.85/5.72  tff(c_16522, plain, (![B_834]: (r2_hidden(k1_yellow_0('#skF_7', B_834), '#skF_8') | ~m1_subset_1(k1_yellow_0('#skF_7', B_834), u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_76, c_16205])).
% 12.85/5.72  tff(c_16608, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_7', B_24), '#skF_8') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_16522])).
% 12.85/5.72  tff(c_16649, plain, (![B_835]: (r2_hidden(k1_yellow_0('#skF_7', B_835), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16608])).
% 12.85/5.72  tff(c_16697, plain, (![B_9]: (r2_hidden('#skF_3'(u1_struct_0('#skF_7'), B_9), '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7') | u1_struct_0('#skF_7')=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_1846, c_16649])).
% 12.85/5.72  tff(c_16741, plain, (![B_9]: (r2_hidden('#skF_3'(u1_struct_0('#skF_7'), B_9), '#skF_8') | v2_struct_0('#skF_7') | u1_struct_0('#skF_7')=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_66, c_16697])).
% 12.85/5.72  tff(c_20414, plain, (![B_922]: (r2_hidden('#skF_3'(u1_struct_0('#skF_7'), B_922), '#skF_8') | u1_struct_0('#skF_7')=B_922 | ~m1_subset_1(B_922, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_16741])).
% 12.85/5.72  tff(c_12, plain, (![A_8, B_9]: (~r2_hidden('#skF_3'(A_8, B_9), B_9) | B_9=A_8 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.85/5.72  tff(c_20427, plain, (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_20414, c_12])).
% 12.85/5.72  tff(c_20447, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20427])).
% 12.85/5.72  tff(c_383, plain, (![A_135, C_136, B_137]: (m1_subset_1(A_135, C_136) | ~m1_subset_1(B_137, k1_zfmisc_1(C_136)) | ~r2_hidden(A_135, B_137))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.85/5.72  tff(c_395, plain, (![A_135]: (m1_subset_1(A_135, u1_struct_0('#skF_7')) | ~r2_hidden(A_135, '#skF_8'))), inference(resolution, [status(thm)], [c_58, c_383])).
% 12.85/5.72  tff(c_342, plain, (![C_122, B_123, A_124]: (r2_hidden(C_122, B_123) | ~r2_hidden(C_122, A_124) | ~r1_tarski(A_124, B_123))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.85/5.72  tff(c_852, plain, (![A_175, B_176, B_177]: (r2_hidden('#skF_1'(A_175, B_176), B_177) | ~r1_tarski(A_175, B_177) | r1_tarski(A_175, B_176))), inference(resolution, [status(thm)], [c_6, c_342])).
% 12.85/5.72  tff(c_263, plain, (![A_109, B_110]: (r2_hidden(A_109, B_110) | v1_xboole_0(B_110) | ~m1_subset_1(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.85/5.72  tff(c_519, plain, (![A_152, B_153]: (r1_tarski(A_152, B_153) | v1_xboole_0(B_153) | ~m1_subset_1('#skF_1'(A_152, B_153), B_153))), inference(resolution, [status(thm)], [c_263, c_4])).
% 12.85/5.72  tff(c_527, plain, (![A_152]: (r1_tarski(A_152, u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7')) | ~r2_hidden('#skF_1'(A_152, u1_struct_0('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_395, c_519])).
% 12.85/5.72  tff(c_532, plain, (![A_152]: (r1_tarski(A_152, u1_struct_0('#skF_7')) | ~r2_hidden('#skF_1'(A_152, u1_struct_0('#skF_7')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_367, c_527])).
% 12.85/5.72  tff(c_881, plain, (![A_175]: (~r1_tarski(A_175, '#skF_8') | r1_tarski(A_175, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_852, c_532])).
% 12.85/5.72  tff(c_22, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.85/5.72  tff(c_1086, plain, (![A_192, B_193, B_194]: (r2_hidden(A_192, B_193) | ~r1_tarski(B_194, B_193) | v1_xboole_0(B_194) | ~m1_subset_1(A_192, B_194))), inference(resolution, [status(thm)], [c_22, c_342])).
% 12.85/5.72  tff(c_1541, plain, (![A_227, A_228]: (r2_hidden(A_227, u1_struct_0('#skF_7')) | v1_xboole_0(A_228) | ~m1_subset_1(A_227, A_228) | ~r1_tarski(A_228, '#skF_8'))), inference(resolution, [status(thm)], [c_881, c_1086])).
% 12.85/5.72  tff(c_1559, plain, (![A_135]: (r2_hidden(A_135, u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7')) | ~r1_tarski(u1_struct_0('#skF_7'), '#skF_8') | ~r2_hidden(A_135, '#skF_8'))), inference(resolution, [status(thm)], [c_395, c_1541])).
% 12.85/5.72  tff(c_1586, plain, (![A_135]: (r2_hidden(A_135, u1_struct_0('#skF_7')) | ~r1_tarski(u1_struct_0('#skF_7'), '#skF_8') | ~r2_hidden(A_135, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_367, c_1559])).
% 12.85/5.72  tff(c_1610, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1586])).
% 12.85/5.72  tff(c_20568, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20447, c_1610])).
% 12.85/5.72  tff(c_20604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_20568])).
% 12.85/5.72  tff(c_20606, plain, (r1_tarski(u1_struct_0('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_1586])).
% 12.85/5.72  tff(c_349, plain, (![A_14, B_123, B_15]: (r2_hidden(A_14, B_123) | ~r1_tarski(B_15, B_123) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(resolution, [status(thm)], [c_22, c_342])).
% 12.85/5.72  tff(c_20612, plain, (![A_14]: (r2_hidden(A_14, '#skF_8') | v1_xboole_0(u1_struct_0('#skF_7')) | ~m1_subset_1(A_14, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_20606, c_349])).
% 12.85/5.72  tff(c_20693, plain, (![A_925]: (r2_hidden(A_925, '#skF_8') | ~m1_subset_1(A_925, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_367, c_20612])).
% 12.85/5.72  tff(c_20734, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_7', B_24), '#skF_8') | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_20693])).
% 12.85/5.72  tff(c_20754, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_7', B_24), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_20734])).
% 12.85/5.72  tff(c_23790, plain, (![B_1064]: (r2_hidden('#skF_3'(u1_struct_0('#skF_7'), B_1064), '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7') | u1_struct_0('#skF_7')=B_1064 | ~m1_subset_1(B_1064, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_23725, c_20754])).
% 12.85/5.72  tff(c_23859, plain, (![B_1064]: (r2_hidden('#skF_3'(u1_struct_0('#skF_7'), B_1064), '#skF_8') | v2_struct_0('#skF_7') | u1_struct_0('#skF_7')=B_1064 | ~m1_subset_1(B_1064, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_66, c_23790])).
% 12.85/5.72  tff(c_24368, plain, (![B_1075]: (r2_hidden('#skF_3'(u1_struct_0('#skF_7'), B_1075), '#skF_8') | u1_struct_0('#skF_7')=B_1075 | ~m1_subset_1(B_1075, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_23859])).
% 12.85/5.72  tff(c_24375, plain, (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_24368, c_12])).
% 12.85/5.72  tff(c_24387, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24375])).
% 12.85/5.72  tff(c_584, plain, (![A_161]: (r1_tarski(A_161, u1_struct_0('#skF_7')) | ~r2_hidden('#skF_1'(A_161, u1_struct_0('#skF_7')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_367, c_527])).
% 12.85/5.72  tff(c_595, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_584])).
% 12.85/5.72  tff(c_1094, plain, (![A_192]: (r2_hidden(A_192, u1_struct_0('#skF_7')) | v1_xboole_0('#skF_8') | ~m1_subset_1(A_192, '#skF_8'))), inference(resolution, [status(thm)], [c_595, c_1086])).
% 12.85/5.72  tff(c_1120, plain, (![A_195]: (r2_hidden(A_195, u1_struct_0('#skF_7')) | ~m1_subset_1(A_195, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1094])).
% 12.85/5.72  tff(c_1204, plain, (![A_202]: (u1_struct_0('#skF_7')=A_202 | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(A_202)) | ~m1_subset_1('#skF_3'(A_202, u1_struct_0('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_1120, c_12])).
% 12.85/5.72  tff(c_1209, plain, (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_14, c_1204])).
% 12.85/5.72  tff(c_1210, plain, (~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1209])).
% 12.85/5.72  tff(c_24436, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_24387, c_1210])).
% 12.85/5.72  tff(c_24468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_24436])).
% 12.85/5.72  tff(c_24469, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_1209])).
% 12.85/5.72  tff(c_245, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_84])).
% 12.85/5.72  tff(c_24490, plain, (v1_subset_1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24469, c_245])).
% 12.85/5.72  tff(c_24496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_24490])).
% 12.85/5.72  tff(c_24497, plain, (![A_117]: (~r2_hidden(A_117, '#skF_8'))), inference(splitRight, [status(thm)], [c_310])).
% 12.85/5.72  tff(c_24500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24497, c_246])).
% 12.85/5.72  tff(c_24501, plain, (![A_11]: (~v1_xboole_0(A_11))), inference(splitRight, [status(thm)], [c_309])).
% 12.85/5.72  tff(c_8, plain, (![A_6]: (v1_xboole_0('#skF_2'(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.85/5.72  tff(c_24504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24501, c_8])).
% 12.85/5.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.85/5.72  
% 12.85/5.72  Inference rules
% 12.85/5.72  ----------------------
% 12.85/5.72  #Ref     : 0
% 12.85/5.72  #Sup     : 5432
% 12.85/5.72  #Fact    : 0
% 12.85/5.72  #Define  : 0
% 12.85/5.72  #Split   : 55
% 12.85/5.72  #Chain   : 0
% 12.85/5.72  #Close   : 0
% 12.85/5.72  
% 12.85/5.72  Ordering : KBO
% 12.85/5.72  
% 12.85/5.72  Simplification rules
% 12.85/5.72  ----------------------
% 12.85/5.72  #Subsume      : 2097
% 12.85/5.72  #Demod        : 4997
% 12.85/5.72  #Tautology    : 1127
% 12.85/5.72  #SimpNegUnit  : 894
% 12.85/5.72  #BackRed      : 274
% 12.85/5.72  
% 12.85/5.72  #Partial instantiations: 0
% 12.85/5.72  #Strategies tried      : 1
% 12.85/5.72  
% 12.85/5.72  Timing (in seconds)
% 12.85/5.72  ----------------------
% 13.10/5.73  Preprocessing        : 0.37
% 13.10/5.73  Parsing              : 0.20
% 13.10/5.73  CNF conversion       : 0.03
% 13.10/5.73  Main loop            : 4.56
% 13.10/5.73  Inferencing          : 1.12
% 13.10/5.73  Reduction            : 1.57
% 13.10/5.73  Demodulation         : 1.09
% 13.10/5.73  BG Simplification    : 0.10
% 13.10/5.73  Subsumption          : 1.49
% 13.10/5.73  Abstraction          : 0.15
% 13.10/5.73  MUC search           : 0.00
% 13.10/5.73  Cooper               : 0.00
% 13.10/5.73  Total                : 4.98
% 13.10/5.73  Index Insertion      : 0.00
% 13.10/5.73  Index Deletion       : 0.00
% 13.10/5.73  Index Matching       : 0.00
% 13.10/5.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
