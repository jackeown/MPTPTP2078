%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1561+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:04 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 296 expanded)
%              Number of leaves         :   34 ( 118 expanded)
%              Depth                    :   13
%              Number of atoms          :  347 (1148 expanded)
%              Number of equality atoms :   35 ( 233 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( k1_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B
              & k2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_0)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) )
               => ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) )
              & ( ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) )
               => ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

tff(c_58,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_67,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_67])).

tff(c_72,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_76])).

tff(c_82,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_82])).

tff(c_87,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_54,plain,
    ( k2_yellow_0('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != '#skF_4'
    | k1_yellow_0('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_93,plain,
    ( k2_yellow_0('#skF_3',k1_tarski('#skF_4')) != '#skF_4'
    | k1_yellow_0('#skF_3',k1_tarski('#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_54])).

tff(c_94,plain,(
    k1_yellow_0('#skF_3',k1_tarski('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_60,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_95,plain,(
    ! [A_67,B_68,C_69] :
      ( r3_orders_2(A_67,B_68,B_68)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67)
      | ~ v3_orders_2(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ! [B_68] :
      ( r3_orders_2('#skF_3',B_68,B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_100,plain,(
    ! [B_68] :
      ( r3_orders_2('#skF_3',B_68,B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_97])).

tff(c_102,plain,(
    ! [B_70] :
      ( r3_orders_2('#skF_3',B_70,B_70)
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_100])).

tff(c_105,plain,(
    r3_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_189,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_orders_2(A_104,B_105,C_106)
      | ~ r3_orders_2(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_195,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_189])).

tff(c_206,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_195])).

tff(c_207,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_206])).

tff(c_46,plain,(
    ! [A_55,C_61,B_59] :
      ( r2_lattice3(A_55,k1_tarski(C_61),B_59)
      | ~ r1_orders_2(A_55,C_61,B_59)
      | ~ m1_subset_1(C_61,u1_struct_0(A_55))
      | ~ m1_subset_1(B_59,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_28,plain,(
    ! [A_11,B_23,C_29] :
      ( m1_subset_1('#skF_1'(A_11,B_23,C_29),u1_struct_0(A_11))
      | k1_yellow_0(A_11,C_29) = B_23
      | ~ r2_lattice3(A_11,C_29,B_23)
      | ~ m1_subset_1(B_23,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_217,plain,(
    ! [A_119,C_120,B_121] :
      ( r2_lattice3(A_119,C_120,'#skF_1'(A_119,B_121,C_120))
      | k1_yellow_0(A_119,C_120) = B_121
      | ~ r2_lattice3(A_119,C_120,B_121)
      | ~ m1_subset_1(B_121,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ! [A_55,C_61,B_59] :
      ( r1_orders_2(A_55,C_61,B_59)
      | ~ r2_lattice3(A_55,k1_tarski(C_61),B_59)
      | ~ m1_subset_1(C_61,u1_struct_0(A_55))
      | ~ m1_subset_1(B_59,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_881,plain,(
    ! [A_271,C_272,B_273] :
      ( r1_orders_2(A_271,C_272,'#skF_1'(A_271,B_273,k1_tarski(C_272)))
      | ~ m1_subset_1(C_272,u1_struct_0(A_271))
      | ~ m1_subset_1('#skF_1'(A_271,B_273,k1_tarski(C_272)),u1_struct_0(A_271))
      | k1_yellow_0(A_271,k1_tarski(C_272)) = B_273
      | ~ r2_lattice3(A_271,k1_tarski(C_272),B_273)
      | ~ m1_subset_1(B_273,u1_struct_0(A_271))
      | ~ l1_orders_2(A_271)
      | ~ v5_orders_2(A_271) ) ),
    inference(resolution,[status(thm)],[c_217,c_48])).

tff(c_890,plain,(
    ! [A_274,C_275,B_276] :
      ( r1_orders_2(A_274,C_275,'#skF_1'(A_274,B_276,k1_tarski(C_275)))
      | ~ m1_subset_1(C_275,u1_struct_0(A_274))
      | k1_yellow_0(A_274,k1_tarski(C_275)) = B_276
      | ~ r2_lattice3(A_274,k1_tarski(C_275),B_276)
      | ~ m1_subset_1(B_276,u1_struct_0(A_274))
      | ~ l1_orders_2(A_274)
      | ~ v5_orders_2(A_274) ) ),
    inference(resolution,[status(thm)],[c_28,c_881])).

tff(c_24,plain,(
    ! [A_11,B_23,C_29] :
      ( ~ r1_orders_2(A_11,B_23,'#skF_1'(A_11,B_23,C_29))
      | k1_yellow_0(A_11,C_29) = B_23
      | ~ r2_lattice3(A_11,C_29,B_23)
      | ~ m1_subset_1(B_23,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_901,plain,(
    ! [A_277,B_278] :
      ( k1_yellow_0(A_277,k1_tarski(B_278)) = B_278
      | ~ r2_lattice3(A_277,k1_tarski(B_278),B_278)
      | ~ m1_subset_1(B_278,u1_struct_0(A_277))
      | ~ l1_orders_2(A_277)
      | ~ v5_orders_2(A_277) ) ),
    inference(resolution,[status(thm)],[c_890,c_24])).

tff(c_907,plain,(
    ! [A_279,B_280] :
      ( k1_yellow_0(A_279,k1_tarski(B_280)) = B_280
      | ~ v5_orders_2(A_279)
      | ~ r1_orders_2(A_279,B_280,B_280)
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279) ) ),
    inference(resolution,[status(thm)],[c_46,c_901])).

tff(c_917,plain,
    ( k1_yellow_0('#skF_3',k1_tarski('#skF_4')) = '#skF_4'
    | ~ v5_orders_2('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_207,c_907])).

tff(c_932,plain,(
    k1_yellow_0('#skF_3',k1_tarski('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_60,c_917])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_932])).

tff(c_935,plain,(
    k2_yellow_0('#skF_3',k1_tarski('#skF_4')) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_936,plain,(
    k1_yellow_0('#skF_3',k1_tarski('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_954,plain,(
    ! [A_291,C_292] :
      ( r2_lattice3(A_291,C_292,k1_yellow_0(A_291,C_292))
      | ~ r1_yellow_0(A_291,C_292)
      | ~ m1_subset_1(k1_yellow_0(A_291,C_292),u1_struct_0(A_291))
      | ~ l1_orders_2(A_291)
      | ~ v5_orders_2(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_956,plain,
    ( r2_lattice3('#skF_3',k1_tarski('#skF_4'),k1_yellow_0('#skF_3',k1_tarski('#skF_4')))
    | ~ r1_yellow_0('#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_954])).

tff(c_958,plain,
    ( r2_lattice3('#skF_3',k1_tarski('#skF_4'),'#skF_4')
    | ~ r1_yellow_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_936,c_956])).

tff(c_959,plain,(
    ~ r1_yellow_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_937,plain,(
    ! [A_281,B_282,C_283] :
      ( r3_orders_2(A_281,B_282,B_282)
      | ~ m1_subset_1(C_283,u1_struct_0(A_281))
      | ~ m1_subset_1(B_282,u1_struct_0(A_281))
      | ~ l1_orders_2(A_281)
      | ~ v3_orders_2(A_281)
      | v2_struct_0(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_939,plain,(
    ! [B_282] :
      ( r3_orders_2('#skF_3',B_282,B_282)
      | ~ m1_subset_1(B_282,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_937])).

tff(c_942,plain,(
    ! [B_282] :
      ( r3_orders_2('#skF_3',B_282,B_282)
      | ~ m1_subset_1(B_282,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_939])).

tff(c_948,plain,(
    ! [B_284] :
      ( r3_orders_2('#skF_3',B_284,B_284)
      | ~ m1_subset_1(B_284,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_942])).

tff(c_951,plain,(
    r3_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_948])).

tff(c_986,plain,(
    ! [A_306,B_307,C_308] :
      ( r1_orders_2(A_306,B_307,C_308)
      | ~ r3_orders_2(A_306,B_307,C_308)
      | ~ m1_subset_1(C_308,u1_struct_0(A_306))
      | ~ m1_subset_1(B_307,u1_struct_0(A_306))
      | ~ l1_orders_2(A_306)
      | ~ v3_orders_2(A_306)
      | v2_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_990,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_951,c_986])).

tff(c_997,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_990])).

tff(c_998,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_997])).

tff(c_22,plain,(
    ! [A_11,B_23,C_29] :
      ( m1_subset_1('#skF_1'(A_11,B_23,C_29),u1_struct_0(A_11))
      | r1_yellow_0(A_11,C_29)
      | ~ r2_lattice3(A_11,C_29,B_23)
      | ~ m1_subset_1(B_23,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1062,plain,(
    ! [A_327,C_328,B_329] :
      ( r2_lattice3(A_327,C_328,'#skF_1'(A_327,B_329,C_328))
      | r1_yellow_0(A_327,C_328)
      | ~ r2_lattice3(A_327,C_328,B_329)
      | ~ m1_subset_1(B_329,u1_struct_0(A_327))
      | ~ l1_orders_2(A_327)
      | ~ v5_orders_2(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1310,plain,(
    ! [A_402,C_403,B_404] :
      ( r1_orders_2(A_402,C_403,'#skF_1'(A_402,B_404,k1_tarski(C_403)))
      | ~ m1_subset_1(C_403,u1_struct_0(A_402))
      | ~ m1_subset_1('#skF_1'(A_402,B_404,k1_tarski(C_403)),u1_struct_0(A_402))
      | r1_yellow_0(A_402,k1_tarski(C_403))
      | ~ r2_lattice3(A_402,k1_tarski(C_403),B_404)
      | ~ m1_subset_1(B_404,u1_struct_0(A_402))
      | ~ l1_orders_2(A_402)
      | ~ v5_orders_2(A_402) ) ),
    inference(resolution,[status(thm)],[c_1062,c_48])).

tff(c_1319,plain,(
    ! [A_405,C_406,B_407] :
      ( r1_orders_2(A_405,C_406,'#skF_1'(A_405,B_407,k1_tarski(C_406)))
      | ~ m1_subset_1(C_406,u1_struct_0(A_405))
      | r1_yellow_0(A_405,k1_tarski(C_406))
      | ~ r2_lattice3(A_405,k1_tarski(C_406),B_407)
      | ~ m1_subset_1(B_407,u1_struct_0(A_405))
      | ~ l1_orders_2(A_405)
      | ~ v5_orders_2(A_405) ) ),
    inference(resolution,[status(thm)],[c_22,c_1310])).

tff(c_18,plain,(
    ! [A_11,B_23,C_29] :
      ( ~ r1_orders_2(A_11,B_23,'#skF_1'(A_11,B_23,C_29))
      | r1_yellow_0(A_11,C_29)
      | ~ r2_lattice3(A_11,C_29,B_23)
      | ~ m1_subset_1(B_23,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1330,plain,(
    ! [A_408,B_409] :
      ( r1_yellow_0(A_408,k1_tarski(B_409))
      | ~ r2_lattice3(A_408,k1_tarski(B_409),B_409)
      | ~ m1_subset_1(B_409,u1_struct_0(A_408))
      | ~ l1_orders_2(A_408)
      | ~ v5_orders_2(A_408) ) ),
    inference(resolution,[status(thm)],[c_1319,c_18])).

tff(c_1336,plain,(
    ! [A_410,B_411] :
      ( r1_yellow_0(A_410,k1_tarski(B_411))
      | ~ v5_orders_2(A_410)
      | ~ r1_orders_2(A_410,B_411,B_411)
      | ~ m1_subset_1(B_411,u1_struct_0(A_410))
      | ~ l1_orders_2(A_410) ) ),
    inference(resolution,[status(thm)],[c_46,c_1330])).

tff(c_1346,plain,
    ( r1_yellow_0('#skF_3',k1_tarski('#skF_4'))
    | ~ v5_orders_2('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_998,c_1336])).

tff(c_1361,plain,(
    r1_yellow_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_60,c_1346])).

tff(c_1363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_959,c_1361])).

tff(c_1364,plain,(
    r2_lattice3('#skF_3',k1_tarski('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_1368,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_1364,c_48])).

tff(c_1371,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1368])).

tff(c_50,plain,(
    ! [A_55,C_61,B_59] :
      ( r1_lattice3(A_55,k1_tarski(C_61),B_59)
      | ~ r1_orders_2(A_55,B_59,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_55))
      | ~ m1_subset_1(B_59,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_44,plain,(
    ! [A_33,B_45,C_51] :
      ( m1_subset_1('#skF_2'(A_33,B_45,C_51),u1_struct_0(A_33))
      | k2_yellow_0(A_33,C_51) = B_45
      | ~ r1_lattice3(A_33,C_51,B_45)
      | ~ m1_subset_1(B_45,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1551,plain,(
    ! [A_470,C_471,B_472] :
      ( r1_lattice3(A_470,C_471,'#skF_2'(A_470,B_472,C_471))
      | k2_yellow_0(A_470,C_471) = B_472
      | ~ r1_lattice3(A_470,C_471,B_472)
      | ~ m1_subset_1(B_472,u1_struct_0(A_470))
      | ~ l1_orders_2(A_470)
      | ~ v5_orders_2(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    ! [A_55,B_59,C_61] :
      ( r1_orders_2(A_55,B_59,C_61)
      | ~ r1_lattice3(A_55,k1_tarski(C_61),B_59)
      | ~ m1_subset_1(C_61,u1_struct_0(A_55))
      | ~ m1_subset_1(B_59,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1916,plain,(
    ! [A_576,B_577,C_578] :
      ( r1_orders_2(A_576,'#skF_2'(A_576,B_577,k1_tarski(C_578)),C_578)
      | ~ m1_subset_1(C_578,u1_struct_0(A_576))
      | ~ m1_subset_1('#skF_2'(A_576,B_577,k1_tarski(C_578)),u1_struct_0(A_576))
      | k2_yellow_0(A_576,k1_tarski(C_578)) = B_577
      | ~ r1_lattice3(A_576,k1_tarski(C_578),B_577)
      | ~ m1_subset_1(B_577,u1_struct_0(A_576))
      | ~ l1_orders_2(A_576)
      | ~ v5_orders_2(A_576) ) ),
    inference(resolution,[status(thm)],[c_1551,c_52])).

tff(c_1925,plain,(
    ! [A_579,B_580,C_581] :
      ( r1_orders_2(A_579,'#skF_2'(A_579,B_580,k1_tarski(C_581)),C_581)
      | ~ m1_subset_1(C_581,u1_struct_0(A_579))
      | k2_yellow_0(A_579,k1_tarski(C_581)) = B_580
      | ~ r1_lattice3(A_579,k1_tarski(C_581),B_580)
      | ~ m1_subset_1(B_580,u1_struct_0(A_579))
      | ~ l1_orders_2(A_579)
      | ~ v5_orders_2(A_579) ) ),
    inference(resolution,[status(thm)],[c_44,c_1916])).

tff(c_40,plain,(
    ! [A_33,B_45,C_51] :
      ( ~ r1_orders_2(A_33,'#skF_2'(A_33,B_45,C_51),B_45)
      | k2_yellow_0(A_33,C_51) = B_45
      | ~ r1_lattice3(A_33,C_51,B_45)
      | ~ m1_subset_1(B_45,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1936,plain,(
    ! [A_582,C_583] :
      ( k2_yellow_0(A_582,k1_tarski(C_583)) = C_583
      | ~ r1_lattice3(A_582,k1_tarski(C_583),C_583)
      | ~ m1_subset_1(C_583,u1_struct_0(A_582))
      | ~ l1_orders_2(A_582)
      | ~ v5_orders_2(A_582) ) ),
    inference(resolution,[status(thm)],[c_1925,c_40])).

tff(c_1942,plain,(
    ! [A_584,B_585] :
      ( k2_yellow_0(A_584,k1_tarski(B_585)) = B_585
      | ~ v5_orders_2(A_584)
      | ~ r1_orders_2(A_584,B_585,B_585)
      | ~ m1_subset_1(B_585,u1_struct_0(A_584))
      | ~ l1_orders_2(A_584) ) ),
    inference(resolution,[status(thm)],[c_50,c_1936])).

tff(c_1952,plain,
    ( k2_yellow_0('#skF_3',k1_tarski('#skF_4')) = '#skF_4'
    | ~ v5_orders_2('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_1371,c_1942])).

tff(c_1967,plain,(
    k2_yellow_0('#skF_3',k1_tarski('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_60,c_1952])).

tff(c_1969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_935,c_1967])).

%------------------------------------------------------------------------------
