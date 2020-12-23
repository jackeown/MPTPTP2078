%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:59 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 400 expanded)
%              Number of leaves         :   36 ( 144 expanded)
%              Depth                    :   16
%              Number of atoms          :  276 (1339 expanded)
%              Number of equality atoms :   28 (  65 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_112,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_52,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_105,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_56,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_78,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_86,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_78])).

tff(c_68,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_108,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_117,plain,(
    ! [B_65,A_66] :
      ( v1_subset_1(B_65,A_66)
      | B_65 = A_66
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_123,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_127,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_123])).

tff(c_97,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_97])).

tff(c_107,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_128,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_107])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_128])).

tff(c_135,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_159,plain,(
    ! [C_73,A_74,B_75] :
      ( r2_hidden(C_73,A_74)
      | ~ r2_hidden(C_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_165,plain,(
    ! [A_74] :
      ( r2_hidden(k3_yellow_0('#skF_4'),A_74)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_135,c_159])).

tff(c_166,plain,(
    ! [A_76,C_77,B_78] :
      ( m1_subset_1(A_76,C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_178,plain,(
    ! [A_81,B_82,A_83] :
      ( m1_subset_1(A_81,B_82)
      | ~ r2_hidden(A_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_24,c_166])).

tff(c_220,plain,(
    ! [B_90,A_91] :
      ( m1_subset_1(k3_yellow_0('#skF_4'),B_90)
      | ~ r1_tarski(A_91,B_90)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_165,c_178])).

tff(c_228,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_86,c_220])).

tff(c_263,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_266,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_263])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_266])).

tff(c_272,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_10,plain,(
    ! [A_7,B_8,C_12] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_12),A_7)
      | C_12 = B_8
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_58,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_172,plain,(
    ! [A_76] :
      ( m1_subset_1(A_76,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_76,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_166])).

tff(c_30,plain,(
    ! [A_22,B_24] :
      ( r1_orders_2(A_22,k3_yellow_0(A_22),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v1_yellow_0(A_22)
      | ~ v5_orders_2(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4555,plain,(
    ! [D_486,B_487,A_488,C_489] :
      ( r2_hidden(D_486,B_487)
      | ~ r1_orders_2(A_488,C_489,D_486)
      | ~ r2_hidden(C_489,B_487)
      | ~ m1_subset_1(D_486,u1_struct_0(A_488))
      | ~ m1_subset_1(C_489,u1_struct_0(A_488))
      | ~ v13_waybel_0(B_487,A_488)
      | ~ m1_subset_1(B_487,k1_zfmisc_1(u1_struct_0(A_488)))
      | ~ l1_orders_2(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5708,plain,(
    ! [B_608,B_609,A_610] :
      ( r2_hidden(B_608,B_609)
      | ~ r2_hidden(k3_yellow_0(A_610),B_609)
      | ~ m1_subset_1(k3_yellow_0(A_610),u1_struct_0(A_610))
      | ~ v13_waybel_0(B_609,A_610)
      | ~ m1_subset_1(B_609,k1_zfmisc_1(u1_struct_0(A_610)))
      | ~ m1_subset_1(B_608,u1_struct_0(A_610))
      | ~ l1_orders_2(A_610)
      | ~ v1_yellow_0(A_610)
      | ~ v5_orders_2(A_610)
      | v2_struct_0(A_610) ) ),
    inference(resolution,[status(thm)],[c_30,c_4555])).

tff(c_5725,plain,(
    ! [B_608,B_609] :
      ( r2_hidden(B_608,B_609)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_609)
      | ~ v13_waybel_0(B_609,'#skF_4')
      | ~ m1_subset_1(B_609,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_608,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_yellow_0('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_172,c_5708])).

tff(c_5750,plain,(
    ! [B_608,B_609] :
      ( r2_hidden(B_608,B_609)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_609)
      | ~ v13_waybel_0(B_609,'#skF_4')
      | ~ m1_subset_1(B_609,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_608,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_60,c_58,c_56,c_5725])).

tff(c_5753,plain,(
    ! [B_611,B_612] :
      ( r2_hidden(B_611,B_612)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_612)
      | ~ v13_waybel_0(B_612,'#skF_4')
      | ~ m1_subset_1(B_612,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_611,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5750])).

tff(c_5770,plain,(
    ! [B_611] :
      ( r2_hidden(B_611,'#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
      | ~ v13_waybel_0('#skF_5','#skF_4')
      | ~ m1_subset_1(B_611,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_48,c_5753])).

tff(c_5779,plain,(
    ! [B_613] :
      ( r2_hidden(B_613,'#skF_5')
      | ~ m1_subset_1(B_613,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_135,c_5770])).

tff(c_7058,plain,(
    ! [B_680,C_681] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_680,C_681),'#skF_5')
      | C_681 = B_680
      | ~ m1_subset_1(C_681,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_680,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_5779])).

tff(c_4446,plain,(
    ! [A_474,B_475,C_476] :
      ( r2_hidden('#skF_1'(A_474,B_475,C_476),B_475)
      | r2_hidden('#skF_1'(A_474,B_475,C_476),C_476)
      | C_476 = B_475
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_474))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(A_474)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4482,plain,(
    ! [A_474,B_475,C_476,A_3] :
      ( r2_hidden('#skF_1'(A_474,B_475,C_476),A_3)
      | ~ m1_subset_1(B_475,k1_zfmisc_1(A_3))
      | r2_hidden('#skF_1'(A_474,B_475,C_476),C_476)
      | C_476 = B_475
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_474))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(A_474)) ) ),
    inference(resolution,[status(thm)],[c_4446,c_8])).

tff(c_5327,plain,(
    ! [B_580,C_581,A_582] :
      ( ~ m1_subset_1(B_580,k1_zfmisc_1(C_581))
      | C_581 = B_580
      | ~ m1_subset_1(C_581,k1_zfmisc_1(A_582))
      | ~ m1_subset_1(B_580,k1_zfmisc_1(A_582))
      | r2_hidden('#skF_1'(A_582,B_580,C_581),C_581) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4482])).

tff(c_12,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | ~ r2_hidden('#skF_1'(A_7,B_8,C_12),B_8)
      | C_12 = B_8
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5362,plain,(
    ! [A_582,B_580,C_581] :
      ( ~ r2_hidden('#skF_1'(A_582,B_580,C_581),B_580)
      | ~ m1_subset_1(B_580,k1_zfmisc_1(C_581))
      | C_581 = B_580
      | ~ m1_subset_1(C_581,k1_zfmisc_1(A_582))
      | ~ m1_subset_1(B_580,k1_zfmisc_1(A_582)) ) ),
    inference(resolution,[status(thm)],[c_5327,c_12])).

tff(c_7062,plain,(
    ! [C_681] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(C_681))
      | C_681 = '#skF_5'
      | ~ m1_subset_1(C_681,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_7058,c_5362])).

tff(c_7096,plain,(
    ! [C_682] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(C_682))
      | C_682 = '#skF_5'
      | ~ m1_subset_1(C_682,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7062])).

tff(c_7150,plain,(
    ! [A_686] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_686))
      | A_686 = '#skF_5'
      | ~ r1_tarski(A_686,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24,c_7096])).

tff(c_7169,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_7150])).

tff(c_7179,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7169])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_345,plain,(
    ! [A_103,A_104,B_105] :
      ( r2_hidden(A_103,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104))
      | v1_xboole_0(B_105)
      | ~ m1_subset_1(A_103,B_105) ) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_357,plain,(
    ! [A_103] :
      ( r2_hidden(A_103,u1_struct_0('#skF_4'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_103,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_345])).

tff(c_366,plain,(
    ! [A_103] :
      ( r2_hidden(A_103,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_103,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_357])).

tff(c_347,plain,(
    ! [A_103] :
      ( r2_hidden(A_103,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_103,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_272,c_345])).

tff(c_360,plain,(
    ! [A_103] :
      ( r2_hidden(A_103,'#skF_5')
      | ~ m1_subset_1(A_103,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_347])).

tff(c_4394,plain,(
    ! [A_467,B_468,C_469] :
      ( ~ r2_hidden('#skF_1'(A_467,B_468,C_469),C_469)
      | ~ r2_hidden('#skF_1'(A_467,B_468,C_469),B_468)
      | C_469 = B_468
      | ~ m1_subset_1(C_469,k1_zfmisc_1(A_467))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(A_467)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4614,plain,(
    ! [A_498,B_499] :
      ( ~ r2_hidden('#skF_1'(A_498,B_499,'#skF_5'),B_499)
      | B_499 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_498))
      | ~ m1_subset_1(B_499,k1_zfmisc_1(A_498))
      | ~ m1_subset_1('#skF_1'(A_498,B_499,'#skF_5'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_360,c_4394])).

tff(c_4649,plain,(
    ! [A_498] :
      ( u1_struct_0('#skF_4') = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_498))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_498))
      | ~ m1_subset_1('#skF_1'(A_498,u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_366,c_4614])).

tff(c_4734,plain,(
    ! [A_513] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_513))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_513))
      | ~ m1_subset_1('#skF_1'(A_513,u1_struct_0('#skF_4'),'#skF_5'),'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_4649])).

tff(c_4738,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_4734])).

tff(c_4741,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_4738])).

tff(c_4742,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4741])).

tff(c_7223,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7179,c_4742])).

tff(c_7255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_7223])).

tff(c_7256,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4741])).

tff(c_7282,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7256,c_107])).

tff(c_7291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7282])).

tff(c_7292,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4649])).

tff(c_7357,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7292,c_107])).

tff(c_7366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7357])).

tff(c_7367,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_28,plain,(
    ! [A_21] :
      ( m1_subset_1(k3_yellow_0(A_21),u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7375,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7367,c_28])).

tff(c_7379,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7375])).

tff(c_7390,plain,(
    ! [A_689,B_690] :
      ( r2_hidden(A_689,B_690)
      | v1_xboole_0(B_690)
      | ~ m1_subset_1(A_689,B_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [B_59] :
      ( ~ v1_subset_1(B_59,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_92,plain,(
    ! [B_17] :
      ( ~ v1_subset_1(B_17,B_17)
      | ~ r1_tarski(B_17,B_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_95,plain,(
    ! [B_17] : ~ v1_subset_1(B_17,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_74,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_7388,plain,
    ( v1_subset_1('#skF_5','#skF_5')
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7367,c_74])).

tff(c_7389,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_7388])).

tff(c_7393,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_7390,c_7389])).

tff(c_7396,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7379,c_7393])).

tff(c_7398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_7396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.85/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.75  
% 7.85/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.75  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 7.85/2.75  
% 7.85/2.75  %Foreground sorts:
% 7.85/2.75  
% 7.85/2.75  
% 7.85/2.75  %Background operators:
% 7.85/2.75  
% 7.85/2.75  
% 7.85/2.75  %Foreground operators:
% 7.85/2.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.85/2.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.85/2.75  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.85/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.85/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.85/2.75  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.85/2.75  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.85/2.75  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 7.85/2.75  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 7.85/2.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.85/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.85/2.75  tff('#skF_5', type, '#skF_5': $i).
% 7.85/2.75  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.85/2.75  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.85/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.85/2.75  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.85/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.85/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.85/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.85/2.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.85/2.75  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 7.85/2.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.85/2.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.85/2.75  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 7.85/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.85/2.75  
% 7.85/2.77  tff(f_141, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 7.85/2.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.85/2.77  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.85/2.77  tff(f_112, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 7.85/2.77  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.85/2.77  tff(f_68, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.85/2.77  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 7.85/2.77  tff(f_86, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 7.85/2.77  tff(f_105, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 7.85/2.77  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.85/2.77  tff(f_72, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 7.85/2.77  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_56, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.85/2.77  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.85/2.77  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_78, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.85/2.77  tff(c_86, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_78])).
% 7.85/2.77  tff(c_68, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_108, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 7.85/2.77  tff(c_117, plain, (![B_65, A_66]: (v1_subset_1(B_65, A_66) | B_65=A_66 | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.85/2.77  tff(c_123, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_48, c_117])).
% 7.85/2.77  tff(c_127, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_108, c_123])).
% 7.85/2.77  tff(c_97, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.85/2.77  tff(c_102, plain, (u1_struct_0('#skF_4')='#skF_5' | ~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_86, c_97])).
% 7.85/2.77  tff(c_107, plain, (~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_102])).
% 7.85/2.77  tff(c_128, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_107])).
% 7.85/2.77  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_128])).
% 7.85/2.77  tff(c_135, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 7.85/2.77  tff(c_159, plain, (![C_73, A_74, B_75]: (r2_hidden(C_73, A_74) | ~r2_hidden(C_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.85/2.77  tff(c_165, plain, (![A_74]: (r2_hidden(k3_yellow_0('#skF_4'), A_74) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_135, c_159])).
% 7.85/2.77  tff(c_166, plain, (![A_76, C_77, B_78]: (m1_subset_1(A_76, C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.85/2.77  tff(c_178, plain, (![A_81, B_82, A_83]: (m1_subset_1(A_81, B_82) | ~r2_hidden(A_81, A_83) | ~r1_tarski(A_83, B_82))), inference(resolution, [status(thm)], [c_24, c_166])).
% 7.85/2.77  tff(c_220, plain, (![B_90, A_91]: (m1_subset_1(k3_yellow_0('#skF_4'), B_90) | ~r1_tarski(A_91, B_90) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_165, c_178])).
% 7.85/2.77  tff(c_228, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_86, c_220])).
% 7.85/2.77  tff(c_263, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_228])).
% 7.85/2.77  tff(c_266, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_263])).
% 7.85/2.77  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_266])).
% 7.85/2.77  tff(c_272, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_228])).
% 7.85/2.77  tff(c_10, plain, (![A_7, B_8, C_12]: (m1_subset_1('#skF_1'(A_7, B_8, C_12), A_7) | C_12=B_8 | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.85/2.77  tff(c_50, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_60, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_58, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_172, plain, (![A_76]: (m1_subset_1(A_76, u1_struct_0('#skF_4')) | ~r2_hidden(A_76, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_166])).
% 7.85/2.77  tff(c_30, plain, (![A_22, B_24]: (r1_orders_2(A_22, k3_yellow_0(A_22), B_24) | ~m1_subset_1(B_24, u1_struct_0(A_22)) | ~l1_orders_2(A_22) | ~v1_yellow_0(A_22) | ~v5_orders_2(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.85/2.77  tff(c_4555, plain, (![D_486, B_487, A_488, C_489]: (r2_hidden(D_486, B_487) | ~r1_orders_2(A_488, C_489, D_486) | ~r2_hidden(C_489, B_487) | ~m1_subset_1(D_486, u1_struct_0(A_488)) | ~m1_subset_1(C_489, u1_struct_0(A_488)) | ~v13_waybel_0(B_487, A_488) | ~m1_subset_1(B_487, k1_zfmisc_1(u1_struct_0(A_488))) | ~l1_orders_2(A_488))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.85/2.77  tff(c_5708, plain, (![B_608, B_609, A_610]: (r2_hidden(B_608, B_609) | ~r2_hidden(k3_yellow_0(A_610), B_609) | ~m1_subset_1(k3_yellow_0(A_610), u1_struct_0(A_610)) | ~v13_waybel_0(B_609, A_610) | ~m1_subset_1(B_609, k1_zfmisc_1(u1_struct_0(A_610))) | ~m1_subset_1(B_608, u1_struct_0(A_610)) | ~l1_orders_2(A_610) | ~v1_yellow_0(A_610) | ~v5_orders_2(A_610) | v2_struct_0(A_610))), inference(resolution, [status(thm)], [c_30, c_4555])).
% 7.85/2.77  tff(c_5725, plain, (![B_608, B_609]: (r2_hidden(B_608, B_609) | ~r2_hidden(k3_yellow_0('#skF_4'), B_609) | ~v13_waybel_0(B_609, '#skF_4') | ~m1_subset_1(B_609, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_608, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_172, c_5708])).
% 7.85/2.77  tff(c_5750, plain, (![B_608, B_609]: (r2_hidden(B_608, B_609) | ~r2_hidden(k3_yellow_0('#skF_4'), B_609) | ~v13_waybel_0(B_609, '#skF_4') | ~m1_subset_1(B_609, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_608, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_60, c_58, c_56, c_5725])).
% 7.85/2.77  tff(c_5753, plain, (![B_611, B_612]: (r2_hidden(B_611, B_612) | ~r2_hidden(k3_yellow_0('#skF_4'), B_612) | ~v13_waybel_0(B_612, '#skF_4') | ~m1_subset_1(B_612, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_611, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_5750])).
% 7.85/2.77  tff(c_5770, plain, (![B_611]: (r2_hidden(B_611, '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | ~m1_subset_1(B_611, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_48, c_5753])).
% 7.85/2.77  tff(c_5779, plain, (![B_613]: (r2_hidden(B_613, '#skF_5') | ~m1_subset_1(B_613, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_135, c_5770])).
% 7.85/2.77  tff(c_7058, plain, (![B_680, C_681]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_680, C_681), '#skF_5') | C_681=B_680 | ~m1_subset_1(C_681, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_680, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_5779])).
% 7.85/2.77  tff(c_4446, plain, (![A_474, B_475, C_476]: (r2_hidden('#skF_1'(A_474, B_475, C_476), B_475) | r2_hidden('#skF_1'(A_474, B_475, C_476), C_476) | C_476=B_475 | ~m1_subset_1(C_476, k1_zfmisc_1(A_474)) | ~m1_subset_1(B_475, k1_zfmisc_1(A_474)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.85/2.77  tff(c_8, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.85/2.77  tff(c_4482, plain, (![A_474, B_475, C_476, A_3]: (r2_hidden('#skF_1'(A_474, B_475, C_476), A_3) | ~m1_subset_1(B_475, k1_zfmisc_1(A_3)) | r2_hidden('#skF_1'(A_474, B_475, C_476), C_476) | C_476=B_475 | ~m1_subset_1(C_476, k1_zfmisc_1(A_474)) | ~m1_subset_1(B_475, k1_zfmisc_1(A_474)))), inference(resolution, [status(thm)], [c_4446, c_8])).
% 7.85/2.77  tff(c_5327, plain, (![B_580, C_581, A_582]: (~m1_subset_1(B_580, k1_zfmisc_1(C_581)) | C_581=B_580 | ~m1_subset_1(C_581, k1_zfmisc_1(A_582)) | ~m1_subset_1(B_580, k1_zfmisc_1(A_582)) | r2_hidden('#skF_1'(A_582, B_580, C_581), C_581))), inference(factorization, [status(thm), theory('equality')], [c_4482])).
% 7.85/2.77  tff(c_12, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | ~r2_hidden('#skF_1'(A_7, B_8, C_12), B_8) | C_12=B_8 | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.85/2.77  tff(c_5362, plain, (![A_582, B_580, C_581]: (~r2_hidden('#skF_1'(A_582, B_580, C_581), B_580) | ~m1_subset_1(B_580, k1_zfmisc_1(C_581)) | C_581=B_580 | ~m1_subset_1(C_581, k1_zfmisc_1(A_582)) | ~m1_subset_1(B_580, k1_zfmisc_1(A_582)))), inference(resolution, [status(thm)], [c_5327, c_12])).
% 7.85/2.77  tff(c_7062, plain, (![C_681]: (~m1_subset_1('#skF_5', k1_zfmisc_1(C_681)) | C_681='#skF_5' | ~m1_subset_1(C_681, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_7058, c_5362])).
% 7.85/2.77  tff(c_7096, plain, (![C_682]: (~m1_subset_1('#skF_5', k1_zfmisc_1(C_682)) | C_682='#skF_5' | ~m1_subset_1(C_682, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7062])).
% 7.85/2.77  tff(c_7150, plain, (![A_686]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_686)) | A_686='#skF_5' | ~r1_tarski(A_686, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_24, c_7096])).
% 7.85/2.77  tff(c_7169, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_7150])).
% 7.85/2.77  tff(c_7179, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7169])).
% 7.85/2.77  tff(c_20, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.85/2.77  tff(c_345, plain, (![A_103, A_104, B_105]: (r2_hidden(A_103, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)) | v1_xboole_0(B_105) | ~m1_subset_1(A_103, B_105))), inference(resolution, [status(thm)], [c_20, c_159])).
% 7.85/2.77  tff(c_357, plain, (![A_103]: (r2_hidden(A_103, u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5') | ~m1_subset_1(A_103, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_345])).
% 7.85/2.77  tff(c_366, plain, (![A_103]: (r2_hidden(A_103, u1_struct_0('#skF_4')) | ~m1_subset_1(A_103, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_357])).
% 7.85/2.77  tff(c_347, plain, (![A_103]: (r2_hidden(A_103, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(A_103, '#skF_5'))), inference(resolution, [status(thm)], [c_272, c_345])).
% 7.85/2.77  tff(c_360, plain, (![A_103]: (r2_hidden(A_103, '#skF_5') | ~m1_subset_1(A_103, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_347])).
% 7.85/2.77  tff(c_4394, plain, (![A_467, B_468, C_469]: (~r2_hidden('#skF_1'(A_467, B_468, C_469), C_469) | ~r2_hidden('#skF_1'(A_467, B_468, C_469), B_468) | C_469=B_468 | ~m1_subset_1(C_469, k1_zfmisc_1(A_467)) | ~m1_subset_1(B_468, k1_zfmisc_1(A_467)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.85/2.77  tff(c_4614, plain, (![A_498, B_499]: (~r2_hidden('#skF_1'(A_498, B_499, '#skF_5'), B_499) | B_499='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_498)) | ~m1_subset_1(B_499, k1_zfmisc_1(A_498)) | ~m1_subset_1('#skF_1'(A_498, B_499, '#skF_5'), '#skF_5'))), inference(resolution, [status(thm)], [c_360, c_4394])).
% 7.85/2.77  tff(c_4649, plain, (![A_498]: (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_498)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_498)) | ~m1_subset_1('#skF_1'(A_498, u1_struct_0('#skF_4'), '#skF_5'), '#skF_5'))), inference(resolution, [status(thm)], [c_366, c_4614])).
% 7.85/2.77  tff(c_4734, plain, (![A_513]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_513)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_513)) | ~m1_subset_1('#skF_1'(A_513, u1_struct_0('#skF_4'), '#skF_5'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_4649])).
% 7.85/2.77  tff(c_4738, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_4734])).
% 7.85/2.77  tff(c_4741, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_4738])).
% 7.85/2.77  tff(c_4742, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4741])).
% 7.85/2.77  tff(c_7223, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7179, c_4742])).
% 7.85/2.77  tff(c_7255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_7223])).
% 7.85/2.77  tff(c_7256, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_4741])).
% 7.85/2.77  tff(c_7282, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7256, c_107])).
% 7.85/2.77  tff(c_7291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7282])).
% 7.85/2.77  tff(c_7292, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_4649])).
% 7.85/2.77  tff(c_7357, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7292, c_107])).
% 7.85/2.77  tff(c_7366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7357])).
% 7.85/2.77  tff(c_7367, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_102])).
% 7.85/2.77  tff(c_28, plain, (![A_21]: (m1_subset_1(k3_yellow_0(A_21), u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.85/2.77  tff(c_7375, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7367, c_28])).
% 7.85/2.77  tff(c_7379, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_7375])).
% 7.85/2.77  tff(c_7390, plain, (![A_689, B_690]: (r2_hidden(A_689, B_690) | v1_xboole_0(B_690) | ~m1_subset_1(A_689, B_690))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.85/2.77  tff(c_88, plain, (![B_59]: (~v1_subset_1(B_59, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.85/2.77  tff(c_92, plain, (![B_17]: (~v1_subset_1(B_17, B_17) | ~r1_tarski(B_17, B_17))), inference(resolution, [status(thm)], [c_24, c_88])).
% 7.85/2.77  tff(c_95, plain, (![B_17]: (~v1_subset_1(B_17, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92])).
% 7.85/2.77  tff(c_74, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.85/2.77  tff(c_7388, plain, (v1_subset_1('#skF_5', '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7367, c_74])).
% 7.85/2.77  tff(c_7389, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_95, c_7388])).
% 7.85/2.77  tff(c_7393, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_7390, c_7389])).
% 7.85/2.77  tff(c_7396, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7379, c_7393])).
% 7.85/2.77  tff(c_7398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_7396])).
% 7.85/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.77  
% 7.85/2.77  Inference rules
% 7.85/2.77  ----------------------
% 7.85/2.77  #Ref     : 0
% 7.85/2.77  #Sup     : 1507
% 7.85/2.77  #Fact    : 12
% 7.85/2.77  #Define  : 0
% 7.85/2.77  #Split   : 26
% 7.85/2.77  #Chain   : 0
% 7.85/2.77  #Close   : 0
% 7.85/2.77  
% 7.85/2.77  Ordering : KBO
% 7.85/2.77  
% 7.85/2.77  Simplification rules
% 7.85/2.77  ----------------------
% 7.85/2.77  #Subsume      : 453
% 7.85/2.77  #Demod        : 679
% 7.85/2.77  #Tautology    : 186
% 7.85/2.77  #SimpNegUnit  : 52
% 7.85/2.77  #BackRed      : 206
% 7.85/2.77  
% 7.85/2.77  #Partial instantiations: 0
% 7.85/2.77  #Strategies tried      : 1
% 7.85/2.77  
% 7.85/2.77  Timing (in seconds)
% 7.85/2.77  ----------------------
% 7.85/2.77  Preprocessing        : 0.32
% 7.85/2.77  Parsing              : 0.17
% 7.85/2.77  CNF conversion       : 0.03
% 7.85/2.77  Main loop            : 1.68
% 7.85/2.77  Inferencing          : 0.51
% 7.85/2.77  Reduction            : 0.43
% 7.85/2.77  Demodulation         : 0.28
% 7.85/2.77  BG Simplification    : 0.05
% 7.85/2.77  Subsumption          : 0.57
% 7.85/2.77  Abstraction          : 0.06
% 7.85/2.77  MUC search           : 0.00
% 7.85/2.77  Cooper               : 0.00
% 7.85/2.77  Total                : 2.04
% 7.85/2.77  Index Insertion      : 0.00
% 7.85/2.77  Index Deletion       : 0.00
% 7.85/2.77  Index Matching       : 0.00
% 7.85/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
