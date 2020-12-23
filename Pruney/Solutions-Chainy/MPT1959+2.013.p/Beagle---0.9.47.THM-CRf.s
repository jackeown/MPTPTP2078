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
% DateTime   : Thu Dec  3 10:30:59 EST 2020

% Result     : Theorem 14.86s
% Output     : CNFRefutation 15.04s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 299 expanded)
%              Number of leaves         :   39 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  277 ( 963 expanded)
%              Number of equality atoms :   28 (  71 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_119,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_148,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_112,axiom,(
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

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [C_65,A_66] :
      ( r2_hidden(C_65,k1_zfmisc_1(A_66))
      | ~ r1_tarski(C_65,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,(
    ! [C_67,A_68] :
      ( m1_subset_1(C_67,k1_zfmisc_1(A_68))
      | ~ r1_tarski(C_67,A_68) ) ),
    inference(resolution,[status(thm)],[c_91,c_32])).

tff(c_56,plain,(
    ! [B_56] :
      ( ~ v1_subset_1(B_56,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_104,plain,(
    ! [A_68] :
      ( ~ v1_subset_1(A_68,A_68)
      | ~ r1_tarski(A_68,A_68) ) ),
    inference(resolution,[status(thm)],[c_100,c_56])).

tff(c_107,plain,(
    ! [A_68] : ~ v1_subset_1(A_68,A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_104])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_99,plain,(
    ! [C_65,A_66] :
      ( m1_subset_1(C_65,k1_zfmisc_1(A_66))
      | ~ r1_tarski(C_65,A_66) ) ),
    inference(resolution,[status(thm)],[c_91,c_32])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_213,plain,(
    ! [C_84,A_85,B_86] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_416,plain,(
    ! [C_114,A_115,A_116] :
      ( r2_hidden(C_114,A_115)
      | ~ m1_subset_1(k1_zfmisc_1(A_116),k1_zfmisc_1(A_115))
      | ~ r1_tarski(C_114,A_116) ) ),
    inference(resolution,[status(thm)],[c_10,c_213])).

tff(c_421,plain,(
    ! [C_117,A_118,A_119] :
      ( r2_hidden(C_117,A_118)
      | ~ r1_tarski(C_117,A_119)
      | ~ r1_tarski(k1_zfmisc_1(A_119),A_118) ) ),
    inference(resolution,[status(thm)],[c_99,c_416])).

tff(c_441,plain,(
    ! [B_122,A_123] :
      ( r2_hidden(B_122,A_123)
      | ~ r1_tarski(k1_zfmisc_1(B_122),A_123) ) ),
    inference(resolution,[status(thm)],[c_6,c_421])).

tff(c_447,plain,(
    ! [B_124] : r2_hidden(B_124,k1_zfmisc_1(B_124)) ),
    inference(resolution,[status(thm)],[c_6,c_441])).

tff(c_462,plain,(
    ! [B_124] : m1_subset_1(B_124,k1_zfmisc_1(B_124)) ),
    inference(resolution,[status(thm)],[c_447,c_32])).

tff(c_14794,plain,(
    ! [A_819,B_820,C_821] :
      ( r2_hidden('#skF_3'(A_819,B_820,C_821),B_820)
      | r2_hidden('#skF_3'(A_819,B_820,C_821),C_821)
      | C_821 = B_820
      | ~ m1_subset_1(C_821,k1_zfmisc_1(A_819))
      | ~ m1_subset_1(B_820,k1_zfmisc_1(A_819)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [C_11,A_8,B_9] :
      ( r2_hidden(C_11,A_8)
      | ~ r2_hidden(C_11,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14842,plain,(
    ! [A_819,B_820,C_821,A_8] :
      ( r2_hidden('#skF_3'(A_819,B_820,C_821),A_8)
      | ~ m1_subset_1(C_821,k1_zfmisc_1(A_8))
      | r2_hidden('#skF_3'(A_819,B_820,C_821),B_820)
      | C_821 = B_820
      | ~ m1_subset_1(C_821,k1_zfmisc_1(A_819))
      | ~ m1_subset_1(B_820,k1_zfmisc_1(A_819)) ) ),
    inference(resolution,[status(thm)],[c_14794,c_20])).

tff(c_17717,plain,(
    ! [C_821,B_820,A_819] :
      ( ~ m1_subset_1(C_821,k1_zfmisc_1(B_820))
      | C_821 = B_820
      | ~ m1_subset_1(C_821,k1_zfmisc_1(A_819))
      | ~ m1_subset_1(B_820,k1_zfmisc_1(A_819))
      | r2_hidden('#skF_3'(A_819,B_820,C_821),B_820) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14842])).

tff(c_22,plain,(
    ! [A_12,B_13,C_17] :
      ( m1_subset_1('#skF_3'(A_12,B_13,C_17),A_12)
      | C_17 = B_13
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_84,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_109,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_111,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(A_70,B_71)
      | v1_xboole_0(B_71)
      | ~ m1_subset_1(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_114,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_111,c_109])).

tff(c_124,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_114])).

tff(c_66,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_78,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_110,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_134,plain,(
    ! [B_74,A_75] :
      ( v1_subset_1(B_74,A_75)
      | B_74 = A_75
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_140,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_58,c_134])).

tff(c_144,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_140])).

tff(c_38,plain,(
    ! [A_26] :
      ( m1_subset_1(k3_yellow_0(A_26),u1_struct_0(A_26))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_150,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_38])).

tff(c_154,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_150])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_154])).

tff(c_157,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_157])).

tff(c_161,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_70,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_68,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_242,plain,(
    ! [A_89,C_90,B_91] :
      ( m1_subset_1(A_89,C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_252,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_242])).

tff(c_40,plain,(
    ! [A_27,B_29] :
      ( r1_orders_2(A_27,k3_yellow_0(A_27),B_29)
      | ~ m1_subset_1(B_29,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | ~ v1_yellow_0(A_27)
      | ~ v5_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15104,plain,(
    ! [D_839,B_840,A_841,C_842] :
      ( r2_hidden(D_839,B_840)
      | ~ r1_orders_2(A_841,C_842,D_839)
      | ~ r2_hidden(C_842,B_840)
      | ~ m1_subset_1(D_839,u1_struct_0(A_841))
      | ~ m1_subset_1(C_842,u1_struct_0(A_841))
      | ~ v13_waybel_0(B_840,A_841)
      | ~ m1_subset_1(B_840,k1_zfmisc_1(u1_struct_0(A_841)))
      | ~ l1_orders_2(A_841) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18643,plain,(
    ! [B_1067,B_1068,A_1069] :
      ( r2_hidden(B_1067,B_1068)
      | ~ r2_hidden(k3_yellow_0(A_1069),B_1068)
      | ~ m1_subset_1(k3_yellow_0(A_1069),u1_struct_0(A_1069))
      | ~ v13_waybel_0(B_1068,A_1069)
      | ~ m1_subset_1(B_1068,k1_zfmisc_1(u1_struct_0(A_1069)))
      | ~ m1_subset_1(B_1067,u1_struct_0(A_1069))
      | ~ l1_orders_2(A_1069)
      | ~ v1_yellow_0(A_1069)
      | ~ v5_orders_2(A_1069)
      | v2_struct_0(A_1069) ) ),
    inference(resolution,[status(thm)],[c_40,c_15104])).

tff(c_18657,plain,(
    ! [B_1067,B_1068] :
      ( r2_hidden(B_1067,B_1068)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_1068)
      | ~ v13_waybel_0(B_1068,'#skF_6')
      | ~ m1_subset_1(B_1068,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_1067,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_yellow_0('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_252,c_18643])).

tff(c_18681,plain,(
    ! [B_1067,B_1068] :
      ( r2_hidden(B_1067,B_1068)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_1068)
      | ~ v13_waybel_0(B_1068,'#skF_6')
      | ~ m1_subset_1(B_1068,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_1067,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_70,c_68,c_66,c_18657])).

tff(c_18688,plain,(
    ! [B_1070,B_1071] :
      ( r2_hidden(B_1070,B_1071)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_1071)
      | ~ v13_waybel_0(B_1071,'#skF_6')
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_1070,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_18681])).

tff(c_18771,plain,(
    ! [B_1070] :
      ( r2_hidden(B_1070,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ m1_subset_1(B_1070,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_58,c_18688])).

tff(c_18805,plain,(
    ! [B_1072] :
      ( r2_hidden(B_1072,'#skF_7')
      | ~ m1_subset_1(B_1072,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_161,c_18771])).

tff(c_28834,plain,(
    ! [B_1382,C_1383] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_1382,C_1383),'#skF_7')
      | C_1383 = B_1382
      | ~ m1_subset_1(C_1383,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_1382,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_18805])).

tff(c_24,plain,(
    ! [A_12,B_13,C_17] :
      ( ~ r2_hidden('#skF_3'(A_12,B_13,C_17),C_17)
      | ~ r2_hidden('#skF_3'(A_12,B_13,C_17),B_13)
      | C_17 = B_13
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28847,plain,(
    ! [B_1382] :
      ( ~ r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_1382,'#skF_7'),B_1382)
      | B_1382 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_1382,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_28834,c_24])).

tff(c_29131,plain,(
    ! [B_1387] :
      ( ~ r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_1387,'#skF_7'),B_1387)
      | B_1387 = '#skF_7'
      | ~ m1_subset_1(B_1387,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28847])).

tff(c_29139,plain,(
    ! [B_820] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(B_820))
      | B_820 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_820,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_17717,c_29131])).

tff(c_29247,plain,(
    ! [B_1388] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(B_1388))
      | B_1388 = '#skF_7'
      | ~ m1_subset_1(B_1388,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_29139])).

tff(c_29375,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_462,c_29247])).

tff(c_29425,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_29375])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_672,plain,(
    ! [A_152,A_153,B_154] :
      ( r2_hidden(A_152,A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153))
      | v1_xboole_0(B_154)
      | ~ m1_subset_1(A_152,B_154) ) ),
    inference(resolution,[status(thm)],[c_34,c_213])).

tff(c_684,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_152,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_672])).

tff(c_691,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_152,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_684])).

tff(c_14568,plain,(
    ! [A_798,B_799,C_800] :
      ( ~ r2_hidden('#skF_3'(A_798,B_799,C_800),C_800)
      | ~ r2_hidden('#skF_3'(A_798,B_799,C_800),B_799)
      | C_800 = B_799
      | ~ m1_subset_1(C_800,k1_zfmisc_1(A_798))
      | ~ m1_subset_1(B_799,k1_zfmisc_1(A_798)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16705,plain,(
    ! [A_934,B_935,B_936] :
      ( ~ r2_hidden('#skF_3'(A_934,B_935,B_936),B_935)
      | B_936 = B_935
      | ~ m1_subset_1(B_936,k1_zfmisc_1(A_934))
      | ~ m1_subset_1(B_935,k1_zfmisc_1(A_934))
      | v1_xboole_0(B_936)
      | ~ m1_subset_1('#skF_3'(A_934,B_935,B_936),B_936) ) ),
    inference(resolution,[status(thm)],[c_34,c_14568])).

tff(c_16803,plain,(
    ! [B_944,A_945] :
      ( u1_struct_0('#skF_6') = B_944
      | ~ m1_subset_1(B_944,k1_zfmisc_1(A_945))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_945))
      | v1_xboole_0(B_944)
      | ~ m1_subset_1('#skF_3'(A_945,u1_struct_0('#skF_6'),B_944),B_944)
      | ~ m1_subset_1('#skF_3'(A_945,u1_struct_0('#skF_6'),B_944),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_691,c_16705])).

tff(c_16810,plain,(
    ! [A_12] :
      ( v1_xboole_0(A_12)
      | ~ m1_subset_1('#skF_3'(A_12,u1_struct_0('#skF_6'),A_12),'#skF_7')
      | u1_struct_0('#skF_6') = A_12
      | ~ m1_subset_1(A_12,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_22,c_16803])).

tff(c_17006,plain,(
    ! [A_961] :
      ( v1_xboole_0(A_961)
      | ~ m1_subset_1('#skF_3'(A_961,u1_struct_0('#skF_6'),A_961),'#skF_7')
      | u1_struct_0('#skF_6') = A_961
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_961)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_16810])).

tff(c_17012,plain,
    ( v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_22,c_17006])).

tff(c_17015,plain,
    ( v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_17012])).

tff(c_17016,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_17015])).

tff(c_17017,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_17016])).

tff(c_17021,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_99,c_17017])).

tff(c_29531,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29425,c_17021])).

tff(c_29580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_29531])).

tff(c_29581,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_17016])).

tff(c_160,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_29623,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29581,c_160])).

tff(c_29628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_29623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.86/7.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.86/7.49  
% 14.86/7.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.86/7.49  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 14.86/7.49  
% 14.86/7.49  %Foreground sorts:
% 14.86/7.49  
% 14.86/7.49  
% 14.86/7.49  %Background operators:
% 14.86/7.49  
% 14.86/7.49  
% 14.86/7.49  %Foreground operators:
% 14.86/7.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.86/7.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.86/7.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.86/7.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.86/7.49  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 14.86/7.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 14.86/7.49  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 14.86/7.49  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 14.86/7.49  tff('#skF_7', type, '#skF_7': $i).
% 14.86/7.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.86/7.49  tff('#skF_6', type, '#skF_6': $i).
% 14.86/7.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.86/7.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.86/7.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.86/7.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.86/7.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.86/7.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.86/7.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.86/7.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.86/7.49  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 14.86/7.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.86/7.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.86/7.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.86/7.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 14.86/7.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.86/7.49  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 14.86/7.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.86/7.49  
% 15.04/7.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.04/7.51  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 15.04/7.51  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 15.04/7.51  tff(f_119, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 15.04/7.51  tff(f_148, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 15.04/7.51  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 15.04/7.51  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 15.04/7.51  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 15.04/7.51  tff(f_79, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 15.04/7.51  tff(f_75, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 15.04/7.51  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 15.04/7.51  tff(f_112, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 15.04/7.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.04/7.51  tff(c_91, plain, (![C_65, A_66]: (r2_hidden(C_65, k1_zfmisc_1(A_66)) | ~r1_tarski(C_65, A_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.04/7.51  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.04/7.51  tff(c_100, plain, (![C_67, A_68]: (m1_subset_1(C_67, k1_zfmisc_1(A_68)) | ~r1_tarski(C_67, A_68))), inference(resolution, [status(thm)], [c_91, c_32])).
% 15.04/7.51  tff(c_56, plain, (![B_56]: (~v1_subset_1(B_56, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 15.04/7.51  tff(c_104, plain, (![A_68]: (~v1_subset_1(A_68, A_68) | ~r1_tarski(A_68, A_68))), inference(resolution, [status(thm)], [c_100, c_56])).
% 15.04/7.51  tff(c_107, plain, (![A_68]: (~v1_subset_1(A_68, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_104])).
% 15.04/7.51  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_99, plain, (![C_65, A_66]: (m1_subset_1(C_65, k1_zfmisc_1(A_66)) | ~r1_tarski(C_65, A_66))), inference(resolution, [status(thm)], [c_91, c_32])).
% 15.04/7.51  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.04/7.51  tff(c_213, plain, (![C_84, A_85, B_86]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.04/7.51  tff(c_416, plain, (![C_114, A_115, A_116]: (r2_hidden(C_114, A_115) | ~m1_subset_1(k1_zfmisc_1(A_116), k1_zfmisc_1(A_115)) | ~r1_tarski(C_114, A_116))), inference(resolution, [status(thm)], [c_10, c_213])).
% 15.04/7.51  tff(c_421, plain, (![C_117, A_118, A_119]: (r2_hidden(C_117, A_118) | ~r1_tarski(C_117, A_119) | ~r1_tarski(k1_zfmisc_1(A_119), A_118))), inference(resolution, [status(thm)], [c_99, c_416])).
% 15.04/7.51  tff(c_441, plain, (![B_122, A_123]: (r2_hidden(B_122, A_123) | ~r1_tarski(k1_zfmisc_1(B_122), A_123))), inference(resolution, [status(thm)], [c_6, c_421])).
% 15.04/7.51  tff(c_447, plain, (![B_124]: (r2_hidden(B_124, k1_zfmisc_1(B_124)))), inference(resolution, [status(thm)], [c_6, c_441])).
% 15.04/7.51  tff(c_462, plain, (![B_124]: (m1_subset_1(B_124, k1_zfmisc_1(B_124)))), inference(resolution, [status(thm)], [c_447, c_32])).
% 15.04/7.51  tff(c_14794, plain, (![A_819, B_820, C_821]: (r2_hidden('#skF_3'(A_819, B_820, C_821), B_820) | r2_hidden('#skF_3'(A_819, B_820, C_821), C_821) | C_821=B_820 | ~m1_subset_1(C_821, k1_zfmisc_1(A_819)) | ~m1_subset_1(B_820, k1_zfmisc_1(A_819)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.04/7.51  tff(c_20, plain, (![C_11, A_8, B_9]: (r2_hidden(C_11, A_8) | ~r2_hidden(C_11, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.04/7.51  tff(c_14842, plain, (![A_819, B_820, C_821, A_8]: (r2_hidden('#skF_3'(A_819, B_820, C_821), A_8) | ~m1_subset_1(C_821, k1_zfmisc_1(A_8)) | r2_hidden('#skF_3'(A_819, B_820, C_821), B_820) | C_821=B_820 | ~m1_subset_1(C_821, k1_zfmisc_1(A_819)) | ~m1_subset_1(B_820, k1_zfmisc_1(A_819)))), inference(resolution, [status(thm)], [c_14794, c_20])).
% 15.04/7.51  tff(c_17717, plain, (![C_821, B_820, A_819]: (~m1_subset_1(C_821, k1_zfmisc_1(B_820)) | C_821=B_820 | ~m1_subset_1(C_821, k1_zfmisc_1(A_819)) | ~m1_subset_1(B_820, k1_zfmisc_1(A_819)) | r2_hidden('#skF_3'(A_819, B_820, C_821), B_820))), inference(factorization, [status(thm), theory('equality')], [c_14842])).
% 15.04/7.51  tff(c_22, plain, (![A_12, B_13, C_17]: (m1_subset_1('#skF_3'(A_12, B_13, C_17), A_12) | C_17=B_13 | ~m1_subset_1(C_17, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.04/7.51  tff(c_60, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_84, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_109, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 15.04/7.51  tff(c_64, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_111, plain, (![A_70, B_71]: (r2_hidden(A_70, B_71) | v1_xboole_0(B_71) | ~m1_subset_1(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.04/7.51  tff(c_114, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_111, c_109])).
% 15.04/7.51  tff(c_124, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_114])).
% 15.04/7.51  tff(c_66, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_78, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_110, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_78])).
% 15.04/7.51  tff(c_134, plain, (![B_74, A_75]: (v1_subset_1(B_74, A_75) | B_74=A_75 | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 15.04/7.51  tff(c_140, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_58, c_134])).
% 15.04/7.51  tff(c_144, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_110, c_140])).
% 15.04/7.51  tff(c_38, plain, (![A_26]: (m1_subset_1(k3_yellow_0(A_26), u1_struct_0(A_26)) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.04/7.51  tff(c_150, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7') | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_144, c_38])).
% 15.04/7.51  tff(c_154, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_150])).
% 15.04/7.51  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_154])).
% 15.04/7.51  tff(c_157, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 15.04/7.51  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_157])).
% 15.04/7.51  tff(c_161, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 15.04/7.51  tff(c_76, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_70, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_68, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 15.04/7.51  tff(c_242, plain, (![A_89, C_90, B_91]: (m1_subset_1(A_89, C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.04/7.51  tff(c_252, plain, (![A_89]: (m1_subset_1(A_89, u1_struct_0('#skF_6')) | ~r2_hidden(A_89, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_242])).
% 15.04/7.51  tff(c_40, plain, (![A_27, B_29]: (r1_orders_2(A_27, k3_yellow_0(A_27), B_29) | ~m1_subset_1(B_29, u1_struct_0(A_27)) | ~l1_orders_2(A_27) | ~v1_yellow_0(A_27) | ~v5_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_93])).
% 15.04/7.51  tff(c_15104, plain, (![D_839, B_840, A_841, C_842]: (r2_hidden(D_839, B_840) | ~r1_orders_2(A_841, C_842, D_839) | ~r2_hidden(C_842, B_840) | ~m1_subset_1(D_839, u1_struct_0(A_841)) | ~m1_subset_1(C_842, u1_struct_0(A_841)) | ~v13_waybel_0(B_840, A_841) | ~m1_subset_1(B_840, k1_zfmisc_1(u1_struct_0(A_841))) | ~l1_orders_2(A_841))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.04/7.51  tff(c_18643, plain, (![B_1067, B_1068, A_1069]: (r2_hidden(B_1067, B_1068) | ~r2_hidden(k3_yellow_0(A_1069), B_1068) | ~m1_subset_1(k3_yellow_0(A_1069), u1_struct_0(A_1069)) | ~v13_waybel_0(B_1068, A_1069) | ~m1_subset_1(B_1068, k1_zfmisc_1(u1_struct_0(A_1069))) | ~m1_subset_1(B_1067, u1_struct_0(A_1069)) | ~l1_orders_2(A_1069) | ~v1_yellow_0(A_1069) | ~v5_orders_2(A_1069) | v2_struct_0(A_1069))), inference(resolution, [status(thm)], [c_40, c_15104])).
% 15.04/7.51  tff(c_18657, plain, (![B_1067, B_1068]: (r2_hidden(B_1067, B_1068) | ~r2_hidden(k3_yellow_0('#skF_6'), B_1068) | ~v13_waybel_0(B_1068, '#skF_6') | ~m1_subset_1(B_1068, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_1067, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_252, c_18643])).
% 15.04/7.51  tff(c_18681, plain, (![B_1067, B_1068]: (r2_hidden(B_1067, B_1068) | ~r2_hidden(k3_yellow_0('#skF_6'), B_1068) | ~v13_waybel_0(B_1068, '#skF_6') | ~m1_subset_1(B_1068, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_1067, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_70, c_68, c_66, c_18657])).
% 15.04/7.51  tff(c_18688, plain, (![B_1070, B_1071]: (r2_hidden(B_1070, B_1071) | ~r2_hidden(k3_yellow_0('#skF_6'), B_1071) | ~v13_waybel_0(B_1071, '#skF_6') | ~m1_subset_1(B_1071, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_1070, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_18681])).
% 15.04/7.51  tff(c_18771, plain, (![B_1070]: (r2_hidden(B_1070, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~m1_subset_1(B_1070, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_58, c_18688])).
% 15.04/7.51  tff(c_18805, plain, (![B_1072]: (r2_hidden(B_1072, '#skF_7') | ~m1_subset_1(B_1072, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_161, c_18771])).
% 15.04/7.51  tff(c_28834, plain, (![B_1382, C_1383]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_1382, C_1383), '#skF_7') | C_1383=B_1382 | ~m1_subset_1(C_1383, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_1382, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(resolution, [status(thm)], [c_22, c_18805])).
% 15.04/7.51  tff(c_24, plain, (![A_12, B_13, C_17]: (~r2_hidden('#skF_3'(A_12, B_13, C_17), C_17) | ~r2_hidden('#skF_3'(A_12, B_13, C_17), B_13) | C_17=B_13 | ~m1_subset_1(C_17, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.04/7.51  tff(c_28847, plain, (![B_1382]: (~r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_1382, '#skF_7'), B_1382) | B_1382='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_1382, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(resolution, [status(thm)], [c_28834, c_24])).
% 15.04/7.51  tff(c_29131, plain, (![B_1387]: (~r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_1387, '#skF_7'), B_1387) | B_1387='#skF_7' | ~m1_subset_1(B_1387, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28847])).
% 15.04/7.51  tff(c_29139, plain, (![B_820]: (~m1_subset_1('#skF_7', k1_zfmisc_1(B_820)) | B_820='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_820, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(resolution, [status(thm)], [c_17717, c_29131])).
% 15.04/7.51  tff(c_29247, plain, (![B_1388]: (~m1_subset_1('#skF_7', k1_zfmisc_1(B_1388)) | B_1388='#skF_7' | ~m1_subset_1(B_1388, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_29139])).
% 15.04/7.51  tff(c_29375, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_462, c_29247])).
% 15.04/7.51  tff(c_29425, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_29375])).
% 15.04/7.51  tff(c_34, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.04/7.51  tff(c_672, plain, (![A_152, A_153, B_154]: (r2_hidden(A_152, A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)) | v1_xboole_0(B_154) | ~m1_subset_1(A_152, B_154))), inference(resolution, [status(thm)], [c_34, c_213])).
% 15.04/7.51  tff(c_684, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_152, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_672])).
% 15.04/7.51  tff(c_691, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_6')) | ~m1_subset_1(A_152, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_684])).
% 15.04/7.51  tff(c_14568, plain, (![A_798, B_799, C_800]: (~r2_hidden('#skF_3'(A_798, B_799, C_800), C_800) | ~r2_hidden('#skF_3'(A_798, B_799, C_800), B_799) | C_800=B_799 | ~m1_subset_1(C_800, k1_zfmisc_1(A_798)) | ~m1_subset_1(B_799, k1_zfmisc_1(A_798)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.04/7.51  tff(c_16705, plain, (![A_934, B_935, B_936]: (~r2_hidden('#skF_3'(A_934, B_935, B_936), B_935) | B_936=B_935 | ~m1_subset_1(B_936, k1_zfmisc_1(A_934)) | ~m1_subset_1(B_935, k1_zfmisc_1(A_934)) | v1_xboole_0(B_936) | ~m1_subset_1('#skF_3'(A_934, B_935, B_936), B_936))), inference(resolution, [status(thm)], [c_34, c_14568])).
% 15.04/7.51  tff(c_16803, plain, (![B_944, A_945]: (u1_struct_0('#skF_6')=B_944 | ~m1_subset_1(B_944, k1_zfmisc_1(A_945)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_945)) | v1_xboole_0(B_944) | ~m1_subset_1('#skF_3'(A_945, u1_struct_0('#skF_6'), B_944), B_944) | ~m1_subset_1('#skF_3'(A_945, u1_struct_0('#skF_6'), B_944), '#skF_7'))), inference(resolution, [status(thm)], [c_691, c_16705])).
% 15.04/7.51  tff(c_16810, plain, (![A_12]: (v1_xboole_0(A_12) | ~m1_subset_1('#skF_3'(A_12, u1_struct_0('#skF_6'), A_12), '#skF_7') | u1_struct_0('#skF_6')=A_12 | ~m1_subset_1(A_12, k1_zfmisc_1(A_12)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_22, c_16803])).
% 15.04/7.51  tff(c_17006, plain, (![A_961]: (v1_xboole_0(A_961) | ~m1_subset_1('#skF_3'(A_961, u1_struct_0('#skF_6'), A_961), '#skF_7') | u1_struct_0('#skF_6')=A_961 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_961)))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_16810])).
% 15.04/7.51  tff(c_17012, plain, (v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_22, c_17006])).
% 15.04/7.51  tff(c_17015, plain, (v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_17012])).
% 15.04/7.51  tff(c_17016, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_17015])).
% 15.04/7.51  tff(c_17017, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_17016])).
% 15.04/7.51  tff(c_17021, plain, (~r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_99, c_17017])).
% 15.04/7.51  tff(c_29531, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_29425, c_17021])).
% 15.04/7.51  tff(c_29580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_29531])).
% 15.04/7.51  tff(c_29581, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_17016])).
% 15.04/7.51  tff(c_160, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_84])).
% 15.04/7.51  tff(c_29623, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_29581, c_160])).
% 15.04/7.51  tff(c_29628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_29623])).
% 15.04/7.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.04/7.51  
% 15.04/7.51  Inference rules
% 15.04/7.51  ----------------------
% 15.04/7.51  #Ref     : 0
% 15.04/7.51  #Sup     : 6767
% 15.04/7.51  #Fact    : 18
% 15.04/7.51  #Define  : 0
% 15.04/7.51  #Split   : 29
% 15.04/7.51  #Chain   : 0
% 15.04/7.51  #Close   : 0
% 15.04/7.51  
% 15.04/7.51  Ordering : KBO
% 15.04/7.51  
% 15.04/7.51  Simplification rules
% 15.04/7.51  ----------------------
% 15.04/7.51  #Subsume      : 1045
% 15.04/7.51  #Demod        : 1437
% 15.04/7.51  #Tautology    : 384
% 15.04/7.51  #SimpNegUnit  : 81
% 15.04/7.51  #BackRed      : 466
% 15.04/7.51  
% 15.04/7.51  #Partial instantiations: 0
% 15.04/7.51  #Strategies tried      : 1
% 15.04/7.51  
% 15.04/7.51  Timing (in seconds)
% 15.04/7.51  ----------------------
% 15.04/7.51  Preprocessing        : 0.34
% 15.04/7.51  Parsing              : 0.19
% 15.04/7.51  CNF conversion       : 0.03
% 15.04/7.51  Main loop            : 6.32
% 15.04/7.51  Inferencing          : 1.26
% 15.04/7.51  Reduction            : 1.34
% 15.04/7.51  Demodulation         : 0.85
% 15.04/7.51  BG Simplification    : 0.16
% 15.04/7.51  Subsumption          : 3.12
% 15.04/7.51  Abstraction          : 0.21
% 15.04/7.51  MUC search           : 0.00
% 15.04/7.51  Cooper               : 0.00
% 15.04/7.51  Total                : 6.70
% 15.04/7.51  Index Insertion      : 0.00
% 15.04/7.51  Index Deletion       : 0.00
% 15.04/7.51  Index Matching       : 0.00
% 15.04/7.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
