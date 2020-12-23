%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:01 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 214 expanded)
%              Number of leaves         :   45 (  95 expanded)
%              Depth                    :   23
%              Number of atoms          :  298 ( 920 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_158,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_129,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_122,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_104,axiom,(
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

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_6] : ~ v1_subset_1(k2_subset_1(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_6] : ~ v1_subset_1(A_6,A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_48,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_97,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_95,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_96,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_72])).

tff(c_100,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_97,c_96])).

tff(c_103,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_100])).

tff(c_54,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_104,plain,(
    ! [B_58,A_59] :
      ( v1_subset_1(B_58,A_59)
      | B_58 = A_59
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_107,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_110,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_107])).

tff(c_18,plain,(
    ! [A_13] :
      ( m1_subset_1(k3_yellow_0(A_13),u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_18])).

tff(c_120,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_116])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_120])).

tff(c_123,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1('#skF_1'(A_3,B_4),A_3)
      | B_4 = A_3
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_40,plain,(
    ! [A_45,B_47] :
      ( r1_yellow_0(A_45,k5_waybel_0(A_45,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1542,plain,(
    ! [A_245,B_246] :
      ( k1_yellow_0(A_245,k5_waybel_0(A_245,B_246)) = B_246
      | ~ m1_subset_1(B_246,u1_struct_0(A_245))
      | ~ l1_orders_2(A_245)
      | ~ v5_orders_2(A_245)
      | ~ v4_orders_2(A_245)
      | ~ v3_orders_2(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1556,plain,(
    ! [A_245,B_4] :
      ( k1_yellow_0(A_245,k5_waybel_0(A_245,'#skF_1'(u1_struct_0(A_245),B_4))) = '#skF_1'(u1_struct_0(A_245),B_4)
      | ~ l1_orders_2(A_245)
      | ~ v5_orders_2(A_245)
      | ~ v4_orders_2(A_245)
      | ~ v3_orders_2(A_245)
      | v2_struct_0(A_245)
      | u1_struct_0(A_245) = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_245))) ) ),
    inference(resolution,[status(thm)],[c_8,c_1542])).

tff(c_134,plain,(
    ! [A_64,C_65,B_66] :
      ( m1_subset_1(A_64,C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [A_64] :
      ( m1_subset_1(A_64,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_64,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_134])).

tff(c_56,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_yellow_0(A_19,k1_xboole_0)
      | ~ l1_orders_2(A_19)
      | ~ v1_yellow_0(A_19)
      | ~ v5_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_54] :
      ( k1_yellow_0(A_54,k1_xboole_0) = k3_yellow_0(A_54)
      | ~ l1_orders_2(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    k1_yellow_0('#skF_4',k1_xboole_0) = k3_yellow_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_1500,plain,(
    ! [A_236,B_237,C_238] :
      ( r1_orders_2(A_236,k1_yellow_0(A_236,B_237),k1_yellow_0(A_236,C_238))
      | ~ r1_yellow_0(A_236,C_238)
      | ~ r1_yellow_0(A_236,B_237)
      | ~ r1_tarski(B_237,C_238)
      | ~ l1_orders_2(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1503,plain,(
    ! [C_238] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_238))
      | ~ r1_yellow_0('#skF_4',C_238)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_238)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_1500])).

tff(c_1508,plain,(
    ! [C_238] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_238))
      | ~ r1_yellow_0('#skF_4',C_238)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_1503])).

tff(c_1511,plain,(
    ~ r1_yellow_0('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1508])).

tff(c_1514,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v1_yellow_0('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1511])).

tff(c_1517,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1514])).

tff(c_1519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1517])).

tff(c_1520,plain,(
    ! [C_238] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_238))
      | ~ r1_yellow_0('#skF_4',C_238) ) ),
    inference(splitRight,[status(thm)],[c_1508])).

tff(c_1639,plain,(
    ! [D_254,B_255,A_256,C_257] :
      ( r2_hidden(D_254,B_255)
      | ~ r1_orders_2(A_256,C_257,D_254)
      | ~ r2_hidden(C_257,B_255)
      | ~ m1_subset_1(D_254,u1_struct_0(A_256))
      | ~ m1_subset_1(C_257,u1_struct_0(A_256))
      | ~ v13_waybel_0(B_255,A_256)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_orders_2(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1649,plain,(
    ! [C_238,B_255] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_238),B_255)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_255)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_238),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_255,'#skF_4')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ r1_yellow_0('#skF_4',C_238) ) ),
    inference(resolution,[status(thm)],[c_1520,c_1639])).

tff(c_1668,plain,(
    ! [C_238,B_255] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_238),B_255)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_255)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_238),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_255,'#skF_4')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1649])).

tff(c_1828,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1668])).

tff(c_1831,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_1828])).

tff(c_1838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_1831])).

tff(c_1945,plain,(
    ! [C_276,B_277] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_276),B_277)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_277)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_276),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_277,'#skF_4')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_276) ) ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_1950,plain,(
    ! [B_4,B_277] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_4))),B_277)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_277)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_4),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_277,'#skF_4')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_4)))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1556,c_1945])).

tff(c_1964,plain,(
    ! [B_4,B_277] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_4))),B_277)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_277)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_4),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_277,'#skF_4')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_4)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_1950])).

tff(c_2436,plain,(
    ! [B_346,B_347] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_346))),B_347)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_347)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_346),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_347,'#skF_4')
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_346)))
      | u1_struct_0('#skF_4') = B_346
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1964])).

tff(c_2454,plain,(
    ! [B_4,B_347] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_4),B_347)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_347)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_4),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_347,'#skF_4')
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_4)))
      | u1_struct_0('#skF_4') = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1556,c_2436])).

tff(c_2467,plain,(
    ! [B_4,B_347] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_4),B_347)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_347)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_4),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_347,'#skF_4')
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_4)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2454])).

tff(c_2672,plain,(
    ! [B_364,B_365] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_364),B_365)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_365)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_364),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_365,'#skF_4')
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_364)))
      | u1_struct_0('#skF_4') = B_364
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2467])).

tff(c_2675,plain,(
    ! [B_364,B_365] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_364),B_365)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_365)
      | ~ v13_waybel_0(B_365,'#skF_4')
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_364
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_364),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_2672])).

tff(c_2678,plain,(
    ! [B_364,B_365] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_364),B_365)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_365)
      | ~ v13_waybel_0(B_365,'#skF_4')
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_364
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_364),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2675])).

tff(c_2680,plain,(
    ! [B_366,B_367] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_366),B_367)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_367)
      | ~ v13_waybel_0(B_367,'#skF_4')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_366
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_366),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2678])).

tff(c_2689,plain,(
    ! [B_368,B_369] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_368),B_369)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_369)
      | ~ v13_waybel_0(B_369,'#skF_4')
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_368
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_2680])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | B_4 = A_3
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2717,plain,(
    ! [B_370] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_370)
      | ~ v13_waybel_0(B_370,'#skF_4')
      | u1_struct_0('#skF_4') = B_370
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2689,c_6])).

tff(c_2724,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_2717])).

tff(c_2728,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_123,c_2724])).

tff(c_124,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2767,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2728,c_124])).

tff(c_2770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_2767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:01:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.02  
% 5.41/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.02  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 5.41/2.02  
% 5.41/2.02  %Foreground sorts:
% 5.41/2.02  
% 5.41/2.02  
% 5.41/2.02  %Background operators:
% 5.41/2.02  
% 5.41/2.02  
% 5.41/2.02  %Foreground operators:
% 5.41/2.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.41/2.02  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 5.41/2.02  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.41/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.41/2.02  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.41/2.02  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.41/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.41/2.02  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.41/2.02  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.41/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.41/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.41/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.41/2.02  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 5.41/2.02  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.41/2.02  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 5.41/2.02  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 5.41/2.02  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.41/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.41/2.02  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.41/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.41/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.41/2.02  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.41/2.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.41/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.41/2.02  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.41/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.41/2.02  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 5.41/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.41/2.02  
% 5.41/2.04  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.41/2.04  tff(f_41, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 5.41/2.04  tff(f_158, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 5.41/2.04  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.41/2.04  tff(f_129, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 5.41/2.04  tff(f_61, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 5.41/2.04  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 5.41/2.04  tff(f_122, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 5.41/2.04  tff(f_53, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.41/2.04  tff(f_85, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 5.41/2.04  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.41/2.04  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 5.41/2.04  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 5.41/2.04  tff(f_104, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 5.41/2.04  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.41/2.04  tff(c_10, plain, (![A_6]: (~v1_subset_1(k2_subset_1(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.41/2.04  tff(c_73, plain, (![A_6]: (~v1_subset_1(A_6, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 5.41/2.04  tff(c_48, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_97, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | v1_xboole_0(B_57) | ~m1_subset_1(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.41/2.04  tff(c_66, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_95, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 5.41/2.04  tff(c_72, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_96, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_95, c_72])).
% 5.41/2.04  tff(c_100, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_97, c_96])).
% 5.41/2.04  tff(c_103, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_100])).
% 5.41/2.04  tff(c_54, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_104, plain, (![B_58, A_59]: (v1_subset_1(B_58, A_59) | B_58=A_59 | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.41/2.04  tff(c_107, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_104])).
% 5.41/2.04  tff(c_110, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_95, c_107])).
% 5.41/2.04  tff(c_18, plain, (![A_13]: (m1_subset_1(k3_yellow_0(A_13), u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.41/2.04  tff(c_116, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_110, c_18])).
% 5.41/2.04  tff(c_120, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_116])).
% 5.41/2.04  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_120])).
% 5.41/2.04  tff(c_123, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 5.41/2.04  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1('#skF_1'(A_3, B_4), A_3) | B_4=A_3 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.41/2.04  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_62, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_60, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_58, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_40, plain, (![A_45, B_47]: (r1_yellow_0(A_45, k5_waybel_0(A_45, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_45)) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.41/2.04  tff(c_1542, plain, (![A_245, B_246]: (k1_yellow_0(A_245, k5_waybel_0(A_245, B_246))=B_246 | ~m1_subset_1(B_246, u1_struct_0(A_245)) | ~l1_orders_2(A_245) | ~v5_orders_2(A_245) | ~v4_orders_2(A_245) | ~v3_orders_2(A_245) | v2_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.41/2.04  tff(c_1556, plain, (![A_245, B_4]: (k1_yellow_0(A_245, k5_waybel_0(A_245, '#skF_1'(u1_struct_0(A_245), B_4)))='#skF_1'(u1_struct_0(A_245), B_4) | ~l1_orders_2(A_245) | ~v5_orders_2(A_245) | ~v4_orders_2(A_245) | ~v3_orders_2(A_245) | v2_struct_0(A_245) | u1_struct_0(A_245)=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_245))))), inference(resolution, [status(thm)], [c_8, c_1542])).
% 5.41/2.04  tff(c_134, plain, (![A_64, C_65, B_66]: (m1_subset_1(A_64, C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.41/2.04  tff(c_137, plain, (![A_64]: (m1_subset_1(A_64, u1_struct_0('#skF_4')) | ~r2_hidden(A_64, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_134])).
% 5.41/2.04  tff(c_56, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.04  tff(c_24, plain, (![A_19]: (r1_yellow_0(A_19, k1_xboole_0) | ~l1_orders_2(A_19) | ~v1_yellow_0(A_19) | ~v5_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.41/2.04  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.41/2.04  tff(c_85, plain, (![A_54]: (k1_yellow_0(A_54, k1_xboole_0)=k3_yellow_0(A_54) | ~l1_orders_2(A_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.41/2.04  tff(c_89, plain, (k1_yellow_0('#skF_4', k1_xboole_0)=k3_yellow_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_85])).
% 5.41/2.04  tff(c_1500, plain, (![A_236, B_237, C_238]: (r1_orders_2(A_236, k1_yellow_0(A_236, B_237), k1_yellow_0(A_236, C_238)) | ~r1_yellow_0(A_236, C_238) | ~r1_yellow_0(A_236, B_237) | ~r1_tarski(B_237, C_238) | ~l1_orders_2(A_236))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.41/2.04  tff(c_1503, plain, (![C_238]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_238)) | ~r1_yellow_0('#skF_4', C_238) | ~r1_yellow_0('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_238) | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_1500])).
% 5.41/2.04  tff(c_1508, plain, (![C_238]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_238)) | ~r1_yellow_0('#skF_4', C_238) | ~r1_yellow_0('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_1503])).
% 5.41/2.04  tff(c_1511, plain, (~r1_yellow_0('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1508])).
% 5.41/2.04  tff(c_1514, plain, (~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1511])).
% 5.41/2.04  tff(c_1517, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1514])).
% 5.41/2.04  tff(c_1519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1517])).
% 5.41/2.04  tff(c_1520, plain, (![C_238]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_238)) | ~r1_yellow_0('#skF_4', C_238))), inference(splitRight, [status(thm)], [c_1508])).
% 5.41/2.04  tff(c_1639, plain, (![D_254, B_255, A_256, C_257]: (r2_hidden(D_254, B_255) | ~r1_orders_2(A_256, C_257, D_254) | ~r2_hidden(C_257, B_255) | ~m1_subset_1(D_254, u1_struct_0(A_256)) | ~m1_subset_1(C_257, u1_struct_0(A_256)) | ~v13_waybel_0(B_255, A_256) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_orders_2(A_256))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.04  tff(c_1649, plain, (![C_238, B_255]: (r2_hidden(k1_yellow_0('#skF_4', C_238), B_255) | ~r2_hidden(k3_yellow_0('#skF_4'), B_255) | ~m1_subset_1(k1_yellow_0('#skF_4', C_238), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_255, '#skF_4') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~r1_yellow_0('#skF_4', C_238))), inference(resolution, [status(thm)], [c_1520, c_1639])).
% 5.41/2.04  tff(c_1668, plain, (![C_238, B_255]: (r2_hidden(k1_yellow_0('#skF_4', C_238), B_255) | ~r2_hidden(k3_yellow_0('#skF_4'), B_255) | ~m1_subset_1(k1_yellow_0('#skF_4', C_238), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_255, '#skF_4') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_238))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1649])).
% 5.41/2.04  tff(c_1828, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1668])).
% 5.41/2.04  tff(c_1831, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_137, c_1828])).
% 5.41/2.04  tff(c_1838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_1831])).
% 5.41/2.04  tff(c_1945, plain, (![C_276, B_277]: (r2_hidden(k1_yellow_0('#skF_4', C_276), B_277) | ~r2_hidden(k3_yellow_0('#skF_4'), B_277) | ~m1_subset_1(k1_yellow_0('#skF_4', C_276), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_277, '#skF_4') | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_276))), inference(splitRight, [status(thm)], [c_1668])).
% 5.41/2.04  tff(c_1950, plain, (![B_4, B_277]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_4))), B_277) | ~r2_hidden(k3_yellow_0('#skF_4'), B_277) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_4), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_277, '#skF_4') | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_4))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1556, c_1945])).
% 5.41/2.04  tff(c_1964, plain, (![B_4, B_277]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_4))), B_277) | ~r2_hidden(k3_yellow_0('#skF_4'), B_277) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_4), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_277, '#skF_4') | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_4))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_1950])).
% 5.41/2.04  tff(c_2436, plain, (![B_346, B_347]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_346))), B_347) | ~r2_hidden(k3_yellow_0('#skF_4'), B_347) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_346), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_347, '#skF_4') | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_346))) | u1_struct_0('#skF_4')=B_346 | ~m1_subset_1(B_346, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1964])).
% 5.41/2.04  tff(c_2454, plain, (![B_4, B_347]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_4), B_347) | ~r2_hidden(k3_yellow_0('#skF_4'), B_347) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_4), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_347, '#skF_4') | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_4))) | u1_struct_0('#skF_4')=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1556, c_2436])).
% 5.41/2.04  tff(c_2467, plain, (![B_4, B_347]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_4), B_347) | ~r2_hidden(k3_yellow_0('#skF_4'), B_347) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_4), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_347, '#skF_4') | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_4))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2454])).
% 5.41/2.04  tff(c_2672, plain, (![B_364, B_365]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_364), B_365) | ~r2_hidden(k3_yellow_0('#skF_4'), B_365) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_364), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_365, '#skF_4') | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_364))) | u1_struct_0('#skF_4')=B_364 | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_2467])).
% 5.41/2.04  tff(c_2675, plain, (![B_364, B_365]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_364), B_365) | ~r2_hidden(k3_yellow_0('#skF_4'), B_365) | ~v13_waybel_0(B_365, '#skF_4') | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_364 | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_364), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_2672])).
% 5.41/2.04  tff(c_2678, plain, (![B_364, B_365]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_364), B_365) | ~r2_hidden(k3_yellow_0('#skF_4'), B_365) | ~v13_waybel_0(B_365, '#skF_4') | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_364 | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_364), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2675])).
% 5.41/2.04  tff(c_2680, plain, (![B_366, B_367]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_366), B_367) | ~r2_hidden(k3_yellow_0('#skF_4'), B_367) | ~v13_waybel_0(B_367, '#skF_4') | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_366 | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_366), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_2678])).
% 5.41/2.04  tff(c_2689, plain, (![B_368, B_369]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_368), B_369) | ~r2_hidden(k3_yellow_0('#skF_4'), B_369) | ~v13_waybel_0(B_369, '#skF_4') | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_368 | ~m1_subset_1(B_368, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_8, c_2680])).
% 5.41/2.04  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | B_4=A_3 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.41/2.04  tff(c_2717, plain, (![B_370]: (~r2_hidden(k3_yellow_0('#skF_4'), B_370) | ~v13_waybel_0(B_370, '#skF_4') | u1_struct_0('#skF_4')=B_370 | ~m1_subset_1(B_370, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2689, c_6])).
% 5.41/2.04  tff(c_2724, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_2717])).
% 5.41/2.04  tff(c_2728, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_123, c_2724])).
% 5.41/2.04  tff(c_124, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 5.41/2.04  tff(c_2767, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2728, c_124])).
% 5.41/2.04  tff(c_2770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_2767])).
% 5.41/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.04  
% 5.41/2.04  Inference rules
% 5.41/2.04  ----------------------
% 5.41/2.04  #Ref     : 0
% 5.41/2.04  #Sup     : 516
% 5.41/2.04  #Fact    : 0
% 5.41/2.04  #Define  : 0
% 5.41/2.04  #Split   : 10
% 5.41/2.04  #Chain   : 0
% 5.41/2.04  #Close   : 0
% 5.41/2.04  
% 5.41/2.04  Ordering : KBO
% 5.41/2.04  
% 5.41/2.04  Simplification rules
% 5.41/2.04  ----------------------
% 5.41/2.04  #Subsume      : 78
% 5.41/2.04  #Demod        : 1100
% 5.41/2.04  #Tautology    : 168
% 5.41/2.04  #SimpNegUnit  : 140
% 5.41/2.04  #BackRed      : 79
% 5.41/2.04  
% 5.41/2.04  #Partial instantiations: 0
% 5.41/2.04  #Strategies tried      : 1
% 5.41/2.04  
% 5.41/2.04  Timing (in seconds)
% 5.41/2.04  ----------------------
% 5.41/2.04  Preprocessing        : 0.34
% 5.41/2.04  Parsing              : 0.18
% 5.41/2.04  CNF conversion       : 0.02
% 5.41/2.04  Main loop            : 0.94
% 5.41/2.04  Inferencing          : 0.33
% 5.41/2.04  Reduction            : 0.31
% 5.41/2.04  Demodulation         : 0.22
% 5.41/2.04  BG Simplification    : 0.04
% 5.41/2.04  Subsumption          : 0.21
% 5.41/2.04  Abstraction          : 0.05
% 5.41/2.04  MUC search           : 0.00
% 5.41/2.04  Cooper               : 0.00
% 5.41/2.04  Total                : 1.31
% 5.41/2.04  Index Insertion      : 0.00
% 5.41/2.04  Index Deletion       : 0.00
% 5.41/2.04  Index Matching       : 0.00
% 5.41/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
