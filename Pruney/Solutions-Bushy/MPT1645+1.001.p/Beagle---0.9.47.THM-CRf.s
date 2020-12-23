%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1645+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:11 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 642 expanded)
%              Number of leaves         :   25 ( 226 expanded)
%              Depth                    :   14
%              Number of atoms          :  302 (2363 expanded)
%              Number of equality atoms :  107 ( 718 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v13_waybel_0 > v12_waybel_0 > r1_tarski > m1_subset_1 > l1_orders_2 > k4_waybel_0 > k3_waybel_0 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_waybel_0,type,(
    k3_waybel_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_waybel_0,type,(
    k4_waybel_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( C = D
                       => ( ( v12_waybel_0(C,A)
                           => v12_waybel_0(D,B) )
                          & ( v13_waybel_0(C,A)
                           => v13_waybel_0(D,B) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_0)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> r1_tarski(k4_waybel_0(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( k3_waybel_0(A,C) = k3_waybel_0(B,D)
                        & k4_waybel_0(A,C) = k4_waybel_0(B,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v12_waybel_0(B,A)
          <=> r1_tarski(k3_waybel_0(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_0)).

tff(c_20,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,
    ( v12_waybel_0('#skF_3','#skF_1')
    | ~ v13_waybel_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_41,plain,
    ( v12_waybel_0('#skF_4','#skF_1')
    | ~ v13_waybel_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_733,plain,(
    ~ v13_waybel_0('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_28,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_39,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_30,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_26,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_754,plain,(
    ! [C_154,A_155,D_156,B_157] :
      ( C_154 = A_155
      | g1_orders_2(C_154,D_156) != g1_orders_2(A_155,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_zfmisc_1(A_155,A_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_782,plain,(
    ! [A_162,B_163] :
      ( u1_struct_0('#skF_2') = A_162
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k2_zfmisc_1(A_162,A_162))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_754])).

tff(c_786,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_2')
      | g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_782])).

tff(c_801,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_786])).

tff(c_803,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_801])).

tff(c_36,plain,
    ( ~ v12_waybel_0('#skF_4','#skF_2')
    | v13_waybel_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,
    ( ~ v12_waybel_0('#skF_4','#skF_2')
    | v13_waybel_0('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_47,plain,(
    ~ v12_waybel_0('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_515,plain,(
    ! [C_116,A_117,D_118,B_119] :
      ( C_116 = A_117
      | g1_orders_2(C_116,D_118) != g1_orders_2(A_117,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_550,plain,(
    ! [A_128,B_129] :
      ( u1_struct_0('#skF_2') = A_128
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_515])).

tff(c_554,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_2')
      | g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_550])).

tff(c_562,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_554])).

tff(c_564,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_562])).

tff(c_291,plain,(
    ! [D_81,B_82,C_83,A_84] :
      ( D_81 = B_82
      | g1_orders_2(C_83,D_81) != g1_orders_2(A_84,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_zfmisc_1(A_84,A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_324,plain,(
    ! [B_91,A_92] :
      ( u1_orders_2('#skF_2') = B_91
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_92,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_291])).

tff(c_328,plain,(
    ! [A_1] :
      ( u1_orders_2(A_1) = u1_orders_2('#skF_2')
      | g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_324])).

tff(c_342,plain,
    ( u1_orders_2('#skF_2') = u1_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_328])).

tff(c_344,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_342])).

tff(c_359,plain,
    ( m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_2])).

tff(c_363,plain,(
    m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_359])).

tff(c_355,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_1')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_26])).

tff(c_6,plain,(
    ! [C_6,A_2,D_7,B_3] :
      ( C_6 = A_2
      | g1_orders_2(C_6,D_7) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_373,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_2') = C_6
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7)
      | ~ m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_6])).

tff(c_379,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_2') = C_6
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_373])).

tff(c_403,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_379])).

tff(c_49,plain,(
    ~ v13_waybel_0('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_68,plain,(
    ! [C_45,A_46,D_47,B_48] :
      ( C_45 = A_46
      | g1_orders_2(C_45,D_47) != g1_orders_2(A_46,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_53,B_54] :
      ( u1_struct_0('#skF_2') = A_53
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_zfmisc_1(A_53,A_53))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_89,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_2')
      | g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_110,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_89])).

tff(c_112,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_110])).

tff(c_38,plain,
    ( v12_waybel_0('#skF_3','#skF_1')
    | v13_waybel_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,
    ( v12_waybel_0('#skF_4','#skF_1')
    | v13_waybel_0('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_38])).

tff(c_48,plain,(
    v13_waybel_0('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_74,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k4_waybel_0(A_51,B_52),B_52)
      | ~ v13_waybel_0(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_orders_2(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_76,plain,
    ( r1_tarski(k4_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ v13_waybel_0('#skF_4','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_39,c_74])).

tff(c_81,plain,(
    r1_tarski(k4_waybel_0('#skF_1','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_48,c_76])).

tff(c_146,plain,
    ( m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_159,plain,(
    m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_112,c_146])).

tff(c_134,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_26])).

tff(c_4,plain,(
    ! [D_7,B_3,C_6,A_2] :
      ( D_7 = B_3
      | g1_orders_2(C_6,D_7) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_2') = D_7
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7)
      | ~ m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_4])).

tff(c_178,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_2') = D_7
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_172])).

tff(c_191,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_178])).

tff(c_121,plain,(
    ! [B_60,D_61,A_62] :
      ( k4_waybel_0(B_60,D_61) = k4_waybel_0(A_62,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0(B_60)))
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | g1_orders_2(u1_struct_0(B_60),u1_orders_2(B_60)) != g1_orders_2(u1_struct_0(A_62),u1_orders_2(A_62))
      | ~ l1_orders_2(B_60)
      | ~ l1_orders_2(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_123,plain,(
    ! [A_62] :
      ( k4_waybel_0(A_62,'#skF_4') = k4_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_62)))
      | g1_orders_2(u1_struct_0(A_62),u1_orders_2(A_62)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_39,c_121])).

tff(c_240,plain,(
    ! [A_74] :
      ( k4_waybel_0(A_74,'#skF_4') = k4_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_74)))
      | g1_orders_2(u1_struct_0(A_74),u1_orders_2(A_74)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_123])).

tff(c_242,plain,
    ( k4_waybel_0('#skF_2','#skF_4') = k4_waybel_0('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_240])).

tff(c_246,plain,(
    k4_waybel_0('#skF_2','#skF_4') = k4_waybel_0('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_191,c_112,c_39,c_242])).

tff(c_16,plain,(
    ! [B_28,A_26] :
      ( v13_waybel_0(B_28,A_26)
      | ~ r1_tarski(k4_waybel_0(A_26,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_264,plain,
    ( v13_waybel_0('#skF_4','#skF_2')
    | ~ r1_tarski(k4_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_16])).

tff(c_268,plain,(
    v13_waybel_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_39,c_112,c_81,c_264])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_268])).

tff(c_271,plain,(
    v12_waybel_0('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_296,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k3_waybel_0(A_85,B_86),B_86)
      | ~ v12_waybel_0(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_298,plain,
    ( r1_tarski(k3_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ v12_waybel_0('#skF_4','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_39,c_296])).

tff(c_303,plain,(
    r1_tarski(k3_waybel_0('#skF_1','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_271,c_298])).

tff(c_455,plain,(
    ! [B_106,D_107,A_108] :
      ( k3_waybel_0(B_106,D_107) = k3_waybel_0(A_108,D_107)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0(B_106)))
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | g1_orders_2(u1_struct_0(B_106),u1_orders_2(B_106)) != g1_orders_2(u1_struct_0(A_108),u1_orders_2(A_108))
      | ~ l1_orders_2(B_106)
      | ~ l1_orders_2(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_459,plain,(
    ! [A_108] :
      ( k3_waybel_0(A_108,'#skF_4') = k3_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_108)))
      | g1_orders_2(u1_struct_0(A_108),u1_orders_2(A_108)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ l1_orders_2(A_108) ) ),
    inference(resolution,[status(thm)],[c_39,c_455])).

tff(c_474,plain,(
    ! [A_110] :
      ( k3_waybel_0(A_110,'#skF_4') = k3_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_110)))
      | g1_orders_2(u1_struct_0(A_110),u1_orders_2(A_110)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_459])).

tff(c_476,plain,
    ( k3_waybel_0('#skF_2','#skF_4') = k3_waybel_0('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_474])).

tff(c_480,plain,(
    k3_waybel_0('#skF_2','#skF_4') = k3_waybel_0('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_403,c_344,c_39,c_476])).

tff(c_12,plain,(
    ! [B_25,A_23] :
      ( v12_waybel_0(B_25,A_23)
      | ~ r1_tarski(k3_waybel_0(A_23,B_25),B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_487,plain,
    ( v12_waybel_0('#skF_4','#skF_2')
    | ~ r1_tarski(k3_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_12])).

tff(c_491,plain,(
    v12_waybel_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_39,c_403,c_303,c_487])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_491])).

tff(c_494,plain,(
    v12_waybel_0('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_520,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k3_waybel_0(A_120,B_121),B_121)
      | ~ v12_waybel_0(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_522,plain,
    ( r1_tarski(k3_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ v12_waybel_0('#skF_4','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_39,c_520])).

tff(c_527,plain,(
    r1_tarski(k3_waybel_0('#skF_1','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_494,c_522])).

tff(c_585,plain,
    ( m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_2])).

tff(c_596,plain,(
    m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_564,c_585])).

tff(c_575,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_26])).

tff(c_614,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_2') = D_7
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7)
      | ~ m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_4])).

tff(c_620,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_2') = D_7
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_614])).

tff(c_643,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_620])).

tff(c_622,plain,(
    ! [B_133,D_134,A_135] :
      ( k3_waybel_0(B_133,D_134) = k3_waybel_0(A_135,D_134)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0(B_133)))
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | g1_orders_2(u1_struct_0(B_133),u1_orders_2(B_133)) != g1_orders_2(u1_struct_0(A_135),u1_orders_2(A_135))
      | ~ l1_orders_2(B_133)
      | ~ l1_orders_2(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_626,plain,(
    ! [A_135] :
      ( k3_waybel_0(A_135,'#skF_4') = k3_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_135)))
      | g1_orders_2(u1_struct_0(A_135),u1_orders_2(A_135)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ l1_orders_2(A_135) ) ),
    inference(resolution,[status(thm)],[c_39,c_622])).

tff(c_710,plain,(
    ! [A_148] :
      ( k3_waybel_0(A_148,'#skF_4') = k3_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_148)))
      | g1_orders_2(u1_struct_0(A_148),u1_orders_2(A_148)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_626])).

tff(c_712,plain,
    ( k3_waybel_0('#skF_2','#skF_4') = k3_waybel_0('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_710])).

tff(c_716,plain,(
    k3_waybel_0('#skF_2','#skF_4') = k3_waybel_0('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_643,c_564,c_39,c_712])).

tff(c_723,plain,
    ( v12_waybel_0('#skF_4','#skF_2')
    | ~ r1_tarski(k3_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_12])).

tff(c_727,plain,(
    v12_waybel_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_39,c_564,c_527,c_723])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_727])).

tff(c_730,plain,(
    v13_waybel_0('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_759,plain,(
    ! [A_158,B_159] :
      ( r1_tarski(k4_waybel_0(A_158,B_159),B_159)
      | ~ v13_waybel_0(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_orders_2(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_761,plain,
    ( r1_tarski(k4_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ v13_waybel_0('#skF_4','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_39,c_759])).

tff(c_766,plain,(
    r1_tarski(k4_waybel_0('#skF_1','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_730,c_761])).

tff(c_824,plain,
    ( m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_2])).

tff(c_835,plain,(
    m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_803,c_824])).

tff(c_814,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_26])).

tff(c_858,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_2') = D_7
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7)
      | ~ m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_4])).

tff(c_864,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_2') = D_7
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_858])).

tff(c_889,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_864])).

tff(c_909,plain,(
    ! [B_178,D_179,A_180] :
      ( k4_waybel_0(B_178,D_179) = k4_waybel_0(A_180,D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0(B_178)))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | g1_orders_2(u1_struct_0(B_178),u1_orders_2(B_178)) != g1_orders_2(u1_struct_0(A_180),u1_orders_2(A_180))
      | ~ l1_orders_2(B_178)
      | ~ l1_orders_2(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_913,plain,(
    ! [A_180] :
      ( k4_waybel_0(A_180,'#skF_4') = k4_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_180)))
      | g1_orders_2(u1_struct_0(A_180),u1_orders_2(A_180)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ l1_orders_2(A_180) ) ),
    inference(resolution,[status(thm)],[c_39,c_909])).

tff(c_940,plain,(
    ! [A_185] :
      ( k4_waybel_0(A_185,'#skF_4') = k4_waybel_0('#skF_1','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_185)))
      | g1_orders_2(u1_struct_0(A_185),u1_orders_2(A_185)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_913])).

tff(c_942,plain,
    ( k4_waybel_0('#skF_2','#skF_4') = k4_waybel_0('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_940])).

tff(c_946,plain,(
    k4_waybel_0('#skF_2','#skF_4') = k4_waybel_0('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_889,c_803,c_39,c_942])).

tff(c_964,plain,
    ( v13_waybel_0('#skF_4','#skF_2')
    | ~ r1_tarski(k4_waybel_0('#skF_1','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_16])).

tff(c_968,plain,(
    v13_waybel_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_39,c_803,c_766,c_964])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_733,c_968])).

tff(c_972,plain,(
    v13_waybel_0('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_731,plain,(
    v12_waybel_0('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_32,plain,
    ( ~ v12_waybel_0('#skF_4','#skF_2')
    | ~ v13_waybel_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_731,c_32])).

%------------------------------------------------------------------------------
