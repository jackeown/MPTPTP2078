%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:59 EST 2020

% Result     : Theorem 11.96s
% Output     : CNFRefutation 11.96s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 287 expanded)
%              Number of leaves         :   43 ( 120 expanded)
%              Depth                    :   25
%              Number of atoms          :  300 (1048 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_138,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_167,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_104,plain,(
    ! [B_63] :
      ( ~ v1_subset_1(B_63,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_108,plain,(
    ! [B_10] :
      ( ~ v1_subset_1(B_10,B_10)
      | ~ r1_tarski(B_10,B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_111,plain,(
    ! [B_10] : ~ v1_subset_1(B_10,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_108])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_68,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_66,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_62,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1('#skF_1'(A_4,B_5),A_4)
      | B_5 = A_4
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_23636,plain,(
    ! [A_1234,B_1235] :
      ( k1_yellow_0(A_1234,k5_waybel_0(A_1234,B_1235)) = B_1235
      | ~ m1_subset_1(B_1235,u1_struct_0(A_1234))
      | ~ l1_orders_2(A_1234)
      | ~ v5_orders_2(A_1234)
      | ~ v4_orders_2(A_1234)
      | ~ v3_orders_2(A_1234)
      | v2_struct_0(A_1234) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_23668,plain,(
    ! [A_1234,B_5] :
      ( k1_yellow_0(A_1234,k5_waybel_0(A_1234,'#skF_1'(u1_struct_0(A_1234),B_5))) = '#skF_1'(u1_struct_0(A_1234),B_5)
      | ~ l1_orders_2(A_1234)
      | ~ v5_orders_2(A_1234)
      | ~ v4_orders_2(A_1234)
      | ~ v3_orders_2(A_1234)
      | v2_struct_0(A_1234)
      | u1_struct_0(A_1234) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_1234))) ) ),
    inference(resolution,[status(thm)],[c_12,c_23636])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_yellow_0(A_15,B_16),u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_49,B_51] :
      ( r1_yellow_0(A_49,k5_waybel_0(A_49,B_51))
      | ~ m1_subset_1(B_51,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_23677,plain,(
    ! [A_15,B_16] :
      ( k1_yellow_0(A_15,k5_waybel_0(A_15,k1_yellow_0(A_15,B_16))) = k1_yellow_0(A_15,B_16)
      | ~ v5_orders_2(A_15)
      | ~ v4_orders_2(A_15)
      | ~ v3_orders_2(A_15)
      | v2_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_23636])).

tff(c_56,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_74,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_112,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_155,plain,(
    ! [B_72,A_73] :
      ( v1_subset_1(B_72,A_73)
      | B_72 = A_73
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_161,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_54,c_155])).

tff(c_165,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_161])).

tff(c_85,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_115,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_115])).

tff(c_147,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_147])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_166])).

tff(c_174,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_94,plain,(
    ! [A_61] :
      ( k1_yellow_0(A_61,k1_xboole_0) = k3_yellow_0(A_61)
      | ~ l1_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    k1_yellow_0('#skF_4',k1_xboole_0) = k3_yellow_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_94])).

tff(c_141,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k1_yellow_0(A_70,B_71),u1_struct_0(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_144,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_141])).

tff(c_146,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_144])).

tff(c_176,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_146])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_196,plain,
    ( v1_subset_1('#skF_5','#skF_5')
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_80])).

tff(c_197,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_196])).

tff(c_200,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_203,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_200])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_203])).

tff(c_212,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_32,plain,(
    ! [A_23] :
      ( r1_yellow_0(A_23,k1_xboole_0)
      | ~ l1_orders_2(A_23)
      | ~ v1_yellow_0(A_23)
      | ~ v5_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_23395,plain,(
    ! [A_1206,B_1207,C_1208] :
      ( r1_orders_2(A_1206,k1_yellow_0(A_1206,B_1207),k1_yellow_0(A_1206,C_1208))
      | ~ r1_yellow_0(A_1206,C_1208)
      | ~ r1_yellow_0(A_1206,B_1207)
      | ~ r1_tarski(B_1207,C_1208)
      | ~ l1_orders_2(A_1206) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_23398,plain,(
    ! [C_1208] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_1208))
      | ~ r1_yellow_0('#skF_4',C_1208)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1208)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_23395])).

tff(c_23403,plain,(
    ! [C_1208] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_1208))
      | ~ r1_yellow_0('#skF_4',C_1208)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8,c_23398])).

tff(c_23406,plain,(
    ~ r1_yellow_0('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_23403])).

tff(c_23409,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v1_yellow_0('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_23406])).

tff(c_23412,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_23409])).

tff(c_23414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23412])).

tff(c_23416,plain,(
    r1_yellow_0('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_23403])).

tff(c_245,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1(k1_yellow_0(A_80,B_81),u1_struct_0(A_80))
      | ~ l1_orders_2(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_248,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_245])).

tff(c_250,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_248])).

tff(c_28,plain,(
    ! [A_18,B_21,C_22] :
      ( r1_orders_2(A_18,k1_yellow_0(A_18,B_21),k1_yellow_0(A_18,C_22))
      | ~ r1_yellow_0(A_18,C_22)
      | ~ r1_yellow_0(A_18,B_21)
      | ~ r1_tarski(B_21,C_22)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_23852,plain,(
    ! [D_1243,B_1244,A_1245,C_1246] :
      ( r2_hidden(D_1243,B_1244)
      | ~ r1_orders_2(A_1245,C_1246,D_1243)
      | ~ r2_hidden(C_1246,B_1244)
      | ~ m1_subset_1(D_1243,u1_struct_0(A_1245))
      | ~ m1_subset_1(C_1246,u1_struct_0(A_1245))
      | ~ v13_waybel_0(B_1244,A_1245)
      | ~ m1_subset_1(B_1244,k1_zfmisc_1(u1_struct_0(A_1245)))
      | ~ l1_orders_2(A_1245) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_25594,plain,(
    ! [A_1348,C_1349,B_1350,B_1351] :
      ( r2_hidden(k1_yellow_0(A_1348,C_1349),B_1350)
      | ~ r2_hidden(k1_yellow_0(A_1348,B_1351),B_1350)
      | ~ m1_subset_1(k1_yellow_0(A_1348,C_1349),u1_struct_0(A_1348))
      | ~ m1_subset_1(k1_yellow_0(A_1348,B_1351),u1_struct_0(A_1348))
      | ~ v13_waybel_0(B_1350,A_1348)
      | ~ m1_subset_1(B_1350,k1_zfmisc_1(u1_struct_0(A_1348)))
      | ~ r1_yellow_0(A_1348,C_1349)
      | ~ r1_yellow_0(A_1348,B_1351)
      | ~ r1_tarski(B_1351,C_1349)
      | ~ l1_orders_2(A_1348) ) ),
    inference(resolution,[status(thm)],[c_28,c_23852])).

tff(c_25613,plain,(
    ! [C_1349,B_1350] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1349),B_1350)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1350)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_1349),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k1_yellow_0('#skF_4',k1_xboole_0),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1350,'#skF_4')
      | ~ m1_subset_1(B_1350,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_1349)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1349)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_25594])).

tff(c_25915,plain,(
    ! [C_1370,B_1371] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1370),B_1371)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1371)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_1370),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1371,'#skF_4')
      | ~ m1_subset_1(B_1371,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_1370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8,c_23416,c_250,c_98,c_25613])).

tff(c_25942,plain,(
    ! [B_16,B_1371] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_16),B_1371)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1371)
      | ~ v13_waybel_0(B_1371,'#skF_4')
      | ~ m1_subset_1(B_1371,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',B_16)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_25915])).

tff(c_26504,plain,(
    ! [B_1398,B_1399] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_1398),B_1399)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1399)
      | ~ v13_waybel_0(B_1399,'#skF_4')
      | ~ m1_subset_1(B_1399,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',B_1398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25942])).

tff(c_26524,plain,(
    ! [B_1398] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_1398),'#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
      | ~ v13_waybel_0('#skF_5','#skF_4')
      | ~ r1_yellow_0('#skF_4',B_1398) ) ),
    inference(resolution,[status(thm)],[c_54,c_26504])).

tff(c_26534,plain,(
    ! [B_1400] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_1400),'#skF_5')
      | ~ r1_yellow_0('#skF_4',B_1400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_212,c_26524])).

tff(c_26559,plain,(
    ! [B_16] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_16),'#skF_5')
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',k1_yellow_0('#skF_4',B_16)))
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23677,c_26534])).

tff(c_26592,plain,(
    ! [B_16] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_16),'#skF_5')
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',k1_yellow_0('#skF_4',B_16)))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_70,c_68,c_66,c_26559])).

tff(c_26721,plain,(
    ! [B_1403] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_1403),'#skF_5')
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',k1_yellow_0('#skF_4',B_1403))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_26592])).

tff(c_26753,plain,(
    ! [B_1403] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_1403),'#skF_5')
      | ~ m1_subset_1(k1_yellow_0('#skF_4',B_1403),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_26721])).

tff(c_26776,plain,(
    ! [B_1403] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_1403),'#skF_5')
      | ~ m1_subset_1(k1_yellow_0('#skF_4',B_1403),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_26753])).

tff(c_26933,plain,(
    ! [B_1406] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_1406),'#skF_5')
      | ~ m1_subset_1(k1_yellow_0('#skF_4',B_1406),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_26776])).

tff(c_26980,plain,(
    ! [B_16] :
      ( r2_hidden(k1_yellow_0('#skF_4',B_16),'#skF_5')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_26933])).

tff(c_27017,plain,(
    ! [B_1407] : r2_hidden(k1_yellow_0('#skF_4',B_1407),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_26980])).

tff(c_27042,plain,(
    ! [B_5] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),'#skF_5')
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23668,c_27017])).

tff(c_27075,plain,(
    ! [B_5] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),'#skF_5')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_27042])).

tff(c_27675,plain,(
    ! [B_1437] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1437),'#skF_5')
      | u1_struct_0('#skF_4') = B_1437
      | ~ m1_subset_1(B_1437,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_27075])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | B_5 = A_4
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27692,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_27675,c_10])).

tff(c_27707,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_27692])).

tff(c_216,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_216])).

tff(c_244,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_27741,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27707,c_244])).

tff(c_27749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_27741])).

tff(c_27750,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_213,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_27752,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27750,c_213])).

tff(c_27756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_27752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.96/5.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.96/5.56  
% 11.96/5.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.96/5.56  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 11.96/5.56  
% 11.96/5.56  %Foreground sorts:
% 11.96/5.56  
% 11.96/5.56  
% 11.96/5.56  %Background operators:
% 11.96/5.56  
% 11.96/5.56  
% 11.96/5.56  %Foreground operators:
% 11.96/5.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.96/5.56  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 11.96/5.56  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 11.96/5.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.96/5.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.96/5.56  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 11.96/5.56  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 11.96/5.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.96/5.56  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 11.96/5.56  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 11.96/5.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.96/5.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.96/5.56  tff('#skF_5', type, '#skF_5': $i).
% 11.96/5.56  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 11.96/5.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 11.96/5.56  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 11.96/5.56  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 11.96/5.56  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 11.96/5.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.96/5.56  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 11.96/5.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.96/5.56  tff('#skF_4', type, '#skF_4': $i).
% 11.96/5.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.96/5.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.96/5.56  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 11.96/5.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.96/5.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.96/5.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.96/5.56  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 11.96/5.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.96/5.56  
% 11.96/5.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.96/5.58  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.96/5.58  tff(f_138, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 11.96/5.58  tff(f_167, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 11.96/5.58  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 11.96/5.58  tff(f_131, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_waybel_0)).
% 11.96/5.58  tff(f_66, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 11.96/5.58  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 11.96/5.58  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 11.96/5.58  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.96/5.58  tff(f_94, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 11.96/5.58  tff(f_81, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_yellow_0)).
% 11.96/5.58  tff(f_113, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 11.96/5.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.96/5.58  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.96/5.58  tff(c_104, plain, (![B_63]: (~v1_subset_1(B_63, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.96/5.58  tff(c_108, plain, (![B_10]: (~v1_subset_1(B_10, B_10) | ~r1_tarski(B_10, B_10))), inference(resolution, [status(thm)], [c_18, c_104])).
% 11.96/5.58  tff(c_111, plain, (![B_10]: (~v1_subset_1(B_10, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_108])).
% 11.96/5.58  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_70, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_68, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_66, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_62, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1('#skF_1'(A_4, B_5), A_4) | B_5=A_4 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.96/5.58  tff(c_23636, plain, (![A_1234, B_1235]: (k1_yellow_0(A_1234, k5_waybel_0(A_1234, B_1235))=B_1235 | ~m1_subset_1(B_1235, u1_struct_0(A_1234)) | ~l1_orders_2(A_1234) | ~v5_orders_2(A_1234) | ~v4_orders_2(A_1234) | ~v3_orders_2(A_1234) | v2_struct_0(A_1234))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.96/5.58  tff(c_23668, plain, (![A_1234, B_5]: (k1_yellow_0(A_1234, k5_waybel_0(A_1234, '#skF_1'(u1_struct_0(A_1234), B_5)))='#skF_1'(u1_struct_0(A_1234), B_5) | ~l1_orders_2(A_1234) | ~v5_orders_2(A_1234) | ~v4_orders_2(A_1234) | ~v3_orders_2(A_1234) | v2_struct_0(A_1234) | u1_struct_0(A_1234)=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_1234))))), inference(resolution, [status(thm)], [c_12, c_23636])).
% 11.96/5.58  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(k1_yellow_0(A_15, B_16), u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.96/5.58  tff(c_48, plain, (![A_49, B_51]: (r1_yellow_0(A_49, k5_waybel_0(A_49, B_51)) | ~m1_subset_1(B_51, u1_struct_0(A_49)) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.96/5.58  tff(c_23677, plain, (![A_15, B_16]: (k1_yellow_0(A_15, k5_waybel_0(A_15, k1_yellow_0(A_15, B_16)))=k1_yellow_0(A_15, B_16) | ~v5_orders_2(A_15) | ~v4_orders_2(A_15) | ~v3_orders_2(A_15) | v2_struct_0(A_15) | ~l1_orders_2(A_15))), inference(resolution, [status(thm)], [c_24, c_23636])).
% 11.96/5.58  tff(c_56, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_74, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_112, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_74])).
% 11.96/5.58  tff(c_155, plain, (![B_72, A_73]: (v1_subset_1(B_72, A_73) | B_72=A_73 | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.96/5.58  tff(c_161, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_54, c_155])).
% 11.96/5.58  tff(c_165, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_112, c_161])).
% 11.96/5.58  tff(c_85, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.96/5.58  tff(c_93, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_85])).
% 11.96/5.58  tff(c_115, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.96/5.58  tff(c_122, plain, (u1_struct_0('#skF_4')='#skF_5' | ~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_93, c_115])).
% 11.96/5.58  tff(c_147, plain, (~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_122])).
% 11.96/5.58  tff(c_166, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_147])).
% 11.96/5.58  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_166])).
% 11.96/5.58  tff(c_174, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_122])).
% 11.96/5.58  tff(c_94, plain, (![A_61]: (k1_yellow_0(A_61, k1_xboole_0)=k3_yellow_0(A_61) | ~l1_orders_2(A_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.96/5.58  tff(c_98, plain, (k1_yellow_0('#skF_4', k1_xboole_0)=k3_yellow_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_94])).
% 11.96/5.58  tff(c_141, plain, (![A_70, B_71]: (m1_subset_1(k1_yellow_0(A_70, B_71), u1_struct_0(A_70)) | ~l1_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.96/5.58  tff(c_144, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_98, c_141])).
% 11.96/5.58  tff(c_146, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_144])).
% 11.96/5.58  tff(c_176, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_146])).
% 11.96/5.58  tff(c_60, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.96/5.58  tff(c_80, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_196, plain, (v1_subset_1('#skF_5', '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_80])).
% 11.96/5.58  tff(c_197, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_111, c_196])).
% 11.96/5.58  tff(c_200, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_14, c_197])).
% 11.96/5.58  tff(c_203, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_200])).
% 11.96/5.58  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_203])).
% 11.96/5.58  tff(c_212, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 11.96/5.58  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.96/5.58  tff(c_64, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.96/5.58  tff(c_32, plain, (![A_23]: (r1_yellow_0(A_23, k1_xboole_0) | ~l1_orders_2(A_23) | ~v1_yellow_0(A_23) | ~v5_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.96/5.58  tff(c_23395, plain, (![A_1206, B_1207, C_1208]: (r1_orders_2(A_1206, k1_yellow_0(A_1206, B_1207), k1_yellow_0(A_1206, C_1208)) | ~r1_yellow_0(A_1206, C_1208) | ~r1_yellow_0(A_1206, B_1207) | ~r1_tarski(B_1207, C_1208) | ~l1_orders_2(A_1206))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.96/5.58  tff(c_23398, plain, (![C_1208]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_1208)) | ~r1_yellow_0('#skF_4', C_1208) | ~r1_yellow_0('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1208) | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_23395])).
% 11.96/5.58  tff(c_23403, plain, (![C_1208]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_1208)) | ~r1_yellow_0('#skF_4', C_1208) | ~r1_yellow_0('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8, c_23398])).
% 11.96/5.58  tff(c_23406, plain, (~r1_yellow_0('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_23403])).
% 11.96/5.58  tff(c_23409, plain, (~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_23406])).
% 11.96/5.58  tff(c_23412, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_23409])).
% 11.96/5.58  tff(c_23414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_23412])).
% 11.96/5.58  tff(c_23416, plain, (r1_yellow_0('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_23403])).
% 11.96/5.58  tff(c_245, plain, (![A_80, B_81]: (m1_subset_1(k1_yellow_0(A_80, B_81), u1_struct_0(A_80)) | ~l1_orders_2(A_80))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.96/5.58  tff(c_248, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_98, c_245])).
% 11.96/5.58  tff(c_250, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_248])).
% 11.96/5.58  tff(c_28, plain, (![A_18, B_21, C_22]: (r1_orders_2(A_18, k1_yellow_0(A_18, B_21), k1_yellow_0(A_18, C_22)) | ~r1_yellow_0(A_18, C_22) | ~r1_yellow_0(A_18, B_21) | ~r1_tarski(B_21, C_22) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.96/5.58  tff(c_23852, plain, (![D_1243, B_1244, A_1245, C_1246]: (r2_hidden(D_1243, B_1244) | ~r1_orders_2(A_1245, C_1246, D_1243) | ~r2_hidden(C_1246, B_1244) | ~m1_subset_1(D_1243, u1_struct_0(A_1245)) | ~m1_subset_1(C_1246, u1_struct_0(A_1245)) | ~v13_waybel_0(B_1244, A_1245) | ~m1_subset_1(B_1244, k1_zfmisc_1(u1_struct_0(A_1245))) | ~l1_orders_2(A_1245))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.96/5.58  tff(c_25594, plain, (![A_1348, C_1349, B_1350, B_1351]: (r2_hidden(k1_yellow_0(A_1348, C_1349), B_1350) | ~r2_hidden(k1_yellow_0(A_1348, B_1351), B_1350) | ~m1_subset_1(k1_yellow_0(A_1348, C_1349), u1_struct_0(A_1348)) | ~m1_subset_1(k1_yellow_0(A_1348, B_1351), u1_struct_0(A_1348)) | ~v13_waybel_0(B_1350, A_1348) | ~m1_subset_1(B_1350, k1_zfmisc_1(u1_struct_0(A_1348))) | ~r1_yellow_0(A_1348, C_1349) | ~r1_yellow_0(A_1348, B_1351) | ~r1_tarski(B_1351, C_1349) | ~l1_orders_2(A_1348))), inference(resolution, [status(thm)], [c_28, c_23852])).
% 11.96/5.58  tff(c_25613, plain, (![C_1349, B_1350]: (r2_hidden(k1_yellow_0('#skF_4', C_1349), B_1350) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1350) | ~m1_subset_1(k1_yellow_0('#skF_4', C_1349), u1_struct_0('#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_4', k1_xboole_0), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1350, '#skF_4') | ~m1_subset_1(B_1350, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_1349) | ~r1_yellow_0('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1349) | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_25594])).
% 11.96/5.58  tff(c_25915, plain, (![C_1370, B_1371]: (r2_hidden(k1_yellow_0('#skF_4', C_1370), B_1371) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1371) | ~m1_subset_1(k1_yellow_0('#skF_4', C_1370), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1371, '#skF_4') | ~m1_subset_1(B_1371, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_1370))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8, c_23416, c_250, c_98, c_25613])).
% 11.96/5.58  tff(c_25942, plain, (![B_16, B_1371]: (r2_hidden(k1_yellow_0('#skF_4', B_16), B_1371) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1371) | ~v13_waybel_0(B_1371, '#skF_4') | ~m1_subset_1(B_1371, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', B_16) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_25915])).
% 11.96/5.58  tff(c_26504, plain, (![B_1398, B_1399]: (r2_hidden(k1_yellow_0('#skF_4', B_1398), B_1399) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1399) | ~v13_waybel_0(B_1399, '#skF_4') | ~m1_subset_1(B_1399, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', B_1398))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25942])).
% 11.96/5.58  tff(c_26524, plain, (![B_1398]: (r2_hidden(k1_yellow_0('#skF_4', B_1398), '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | ~r1_yellow_0('#skF_4', B_1398))), inference(resolution, [status(thm)], [c_54, c_26504])).
% 11.96/5.58  tff(c_26534, plain, (![B_1400]: (r2_hidden(k1_yellow_0('#skF_4', B_1400), '#skF_5') | ~r1_yellow_0('#skF_4', B_1400))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_212, c_26524])).
% 11.96/5.58  tff(c_26559, plain, (![B_16]: (r2_hidden(k1_yellow_0('#skF_4', B_16), '#skF_5') | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', k1_yellow_0('#skF_4', B_16))) | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_23677, c_26534])).
% 11.96/5.58  tff(c_26592, plain, (![B_16]: (r2_hidden(k1_yellow_0('#skF_4', B_16), '#skF_5') | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', k1_yellow_0('#skF_4', B_16))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_70, c_68, c_66, c_26559])).
% 11.96/5.58  tff(c_26721, plain, (![B_1403]: (r2_hidden(k1_yellow_0('#skF_4', B_1403), '#skF_5') | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', k1_yellow_0('#skF_4', B_1403))))), inference(negUnitSimplification, [status(thm)], [c_72, c_26592])).
% 11.96/5.58  tff(c_26753, plain, (![B_1403]: (r2_hidden(k1_yellow_0('#skF_4', B_1403), '#skF_5') | ~m1_subset_1(k1_yellow_0('#skF_4', B_1403), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_26721])).
% 11.96/5.58  tff(c_26776, plain, (![B_1403]: (r2_hidden(k1_yellow_0('#skF_4', B_1403), '#skF_5') | ~m1_subset_1(k1_yellow_0('#skF_4', B_1403), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_62, c_26753])).
% 11.96/5.58  tff(c_26933, plain, (![B_1406]: (r2_hidden(k1_yellow_0('#skF_4', B_1406), '#skF_5') | ~m1_subset_1(k1_yellow_0('#skF_4', B_1406), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_26776])).
% 11.96/5.58  tff(c_26980, plain, (![B_16]: (r2_hidden(k1_yellow_0('#skF_4', B_16), '#skF_5') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_26933])).
% 11.96/5.58  tff(c_27017, plain, (![B_1407]: (r2_hidden(k1_yellow_0('#skF_4', B_1407), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_26980])).
% 11.96/5.58  tff(c_27042, plain, (![B_5]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_23668, c_27017])).
% 11.96/5.58  tff(c_27075, plain, (![B_5]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), '#skF_5') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_62, c_27042])).
% 11.96/5.58  tff(c_27675, plain, (![B_1437]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1437), '#skF_5') | u1_struct_0('#skF_4')=B_1437 | ~m1_subset_1(B_1437, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_27075])).
% 11.96/5.58  tff(c_10, plain, (![A_4, B_5]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | B_5=A_4 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.96/5.58  tff(c_27692, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_27675, c_10])).
% 11.96/5.58  tff(c_27707, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_27692])).
% 11.96/5.58  tff(c_216, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.96/5.58  tff(c_223, plain, (u1_struct_0('#skF_4')='#skF_5' | ~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_93, c_216])).
% 11.96/5.58  tff(c_244, plain, (~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_223])).
% 11.96/5.58  tff(c_27741, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27707, c_244])).
% 11.96/5.58  tff(c_27749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_27741])).
% 11.96/5.58  tff(c_27750, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_223])).
% 11.96/5.58  tff(c_213, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_74])).
% 11.96/5.58  tff(c_27752, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27750, c_213])).
% 11.96/5.58  tff(c_27756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_27752])).
% 11.96/5.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.96/5.58  
% 11.96/5.58  Inference rules
% 11.96/5.58  ----------------------
% 11.96/5.58  #Ref     : 0
% 11.96/5.58  #Sup     : 5505
% 11.96/5.58  #Fact    : 8
% 11.96/5.58  #Define  : 0
% 11.96/5.58  #Split   : 71
% 11.96/5.58  #Chain   : 0
% 11.96/5.58  #Close   : 0
% 11.96/5.58  
% 11.96/5.58  Ordering : KBO
% 11.96/5.58  
% 11.96/5.58  Simplification rules
% 11.96/5.58  ----------------------
% 11.96/5.58  #Subsume      : 1426
% 11.96/5.58  #Demod        : 9047
% 11.96/5.58  #Tautology    : 1285
% 11.96/5.58  #SimpNegUnit  : 1385
% 11.96/5.58  #BackRed      : 261
% 11.96/5.58  
% 11.96/5.58  #Partial instantiations: 0
% 11.96/5.58  #Strategies tried      : 1
% 11.96/5.58  
% 11.96/5.58  Timing (in seconds)
% 11.96/5.58  ----------------------
% 11.96/5.59  Preprocessing        : 0.36
% 11.96/5.59  Parsing              : 0.19
% 11.96/5.59  CNF conversion       : 0.03
% 11.96/5.59  Main loop            : 4.41
% 11.96/5.59  Inferencing          : 1.29
% 11.96/5.59  Reduction            : 1.57
% 11.96/5.59  Demodulation         : 1.10
% 11.96/5.59  BG Simplification    : 0.12
% 11.96/5.59  Subsumption          : 1.14
% 11.96/5.59  Abstraction          : 0.18
% 11.96/5.59  MUC search           : 0.00
% 11.96/5.59  Cooper               : 0.00
% 11.96/5.59  Total                : 4.80
% 11.96/5.59  Index Insertion      : 0.00
% 11.96/5.59  Index Deletion       : 0.00
% 11.96/5.59  Index Matching       : 0.00
% 11.96/5.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
