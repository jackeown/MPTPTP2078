%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1798+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:25 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 309 expanded)
%              Number of leaves         :   28 ( 113 expanded)
%              Depth                    :   14
%              Number of atoms          :  326 (1190 expanded)
%              Number of equality atoms :   67 ( 321 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( C = u1_struct_0(B)
                   => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_16,plain,(
    ! [A_29,B_30] :
      ( l1_pre_topc(k8_tmap_1(A_29,B_30))
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_29,B_30] :
      ( v1_pre_topc(k8_tmap_1(A_29,B_30))
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [B_39,A_37] :
      ( m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k5_tmap_1(A_27,B_28),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_29,B_30] :
      ( v2_pre_topc(k8_tmap_1(A_29,B_30))
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_207,plain,(
    ! [A_108,B_109] :
      ( k6_tmap_1(A_108,u1_struct_0(B_109)) = k8_tmap_1(A_108,B_109)
      | ~ m1_subset_1(u1_struct_0(B_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(k8_tmap_1(A_108,B_109))
      | ~ v2_pre_topc(k8_tmap_1(A_108,B_109))
      | ~ v1_pre_topc(k8_tmap_1(A_108,B_109))
      | ~ m1_pre_topc(B_109,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_212,plain,(
    ! [A_110,B_111] :
      ( k6_tmap_1(A_110,u1_struct_0(B_111)) = k8_tmap_1(A_110,B_111)
      | ~ l1_pre_topc(k8_tmap_1(A_110,B_111))
      | ~ v2_pre_topc(k8_tmap_1(A_110,B_111))
      | ~ v1_pre_topc(k8_tmap_1(A_110,B_111))
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110)
      | ~ m1_pre_topc(B_111,A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_26,c_207])).

tff(c_217,plain,(
    ! [A_112,B_113] :
      ( k6_tmap_1(A_112,u1_struct_0(B_113)) = k8_tmap_1(A_112,B_113)
      | ~ l1_pre_topc(k8_tmap_1(A_112,B_113))
      | ~ v1_pre_topc(k8_tmap_1(A_112,B_113))
      | ~ m1_pre_topc(B_113,A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_18,c_212])).

tff(c_222,plain,(
    ! [A_114,B_115] :
      ( k6_tmap_1(A_114,u1_struct_0(B_115)) = k8_tmap_1(A_114,B_115)
      | ~ l1_pre_topc(k8_tmap_1(A_114,B_115))
      | ~ m1_pre_topc(B_115,A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_226,plain,(
    ! [A_29,B_30] :
      ( k6_tmap_1(A_29,u1_struct_0(B_30)) = k8_tmap_1(A_29,B_30)
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_16,c_222])).

tff(c_122,plain,(
    ! [A_79,B_80] :
      ( g1_pre_topc(u1_struct_0(A_79),k5_tmap_1(A_79,B_80)) = k6_tmap_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_126,plain,(
    ! [A_81,B_82] :
      ( g1_pre_topc(u1_struct_0(A_81),k5_tmap_1(A_81,u1_struct_0(B_82))) = k6_tmap_1(A_81,u1_struct_0(B_82))
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ m1_pre_topc(B_82,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_26,c_122])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    ! [C_51,A_52,D_53,B_54] :
      ( C_51 = A_52
      | g1_pre_topc(C_51,D_53) != g1_pre_topc(A_52,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    ! [A_1,A_52,B_54] :
      ( u1_struct_0(A_1) = A_52
      | g1_pre_topc(A_52,B_54) != A_1
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_52)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_267,plain,(
    ! [A_129,A_128,B_130] :
      ( u1_struct_0(A_129) = u1_struct_0(A_128)
      | k6_tmap_1(A_128,u1_struct_0(B_130)) != A_129
      | ~ m1_subset_1(k5_tmap_1(A_128,u1_struct_0(B_130)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128))))
      | ~ v1_pre_topc(A_129)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128)
      | ~ m1_pre_topc(B_130,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_62])).

tff(c_269,plain,(
    ! [A_29,A_129,B_30] :
      ( u1_struct_0(A_29) = u1_struct_0(A_129)
      | k8_tmap_1(A_29,B_30) != A_129
      | ~ m1_subset_1(k5_tmap_1(A_29,u1_struct_0(B_30)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29))))
      | ~ v1_pre_topc(A_129)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_267])).

tff(c_568,plain,(
    ! [A_239,B_240] :
      ( u1_struct_0(k8_tmap_1(A_239,B_240)) = u1_struct_0(A_239)
      | ~ m1_subset_1(k5_tmap_1(A_239,u1_struct_0(B_240)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_239))))
      | ~ v1_pre_topc(k8_tmap_1(A_239,B_240))
      | ~ l1_pre_topc(k8_tmap_1(A_239,B_240))
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239)
      | ~ m1_pre_topc(B_240,A_239)
      | ~ l1_pre_topc(A_239)
      | ~ m1_pre_topc(B_240,A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_269])).

tff(c_577,plain,(
    ! [A_241,B_242] :
      ( u1_struct_0(k8_tmap_1(A_241,B_242)) = u1_struct_0(A_241)
      | ~ v1_pre_topc(k8_tmap_1(A_241,B_242))
      | ~ l1_pre_topc(k8_tmap_1(A_241,B_242))
      | ~ m1_pre_topc(B_242,A_241)
      | ~ m1_subset_1(u1_struct_0(B_242),k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(resolution,[status(thm)],[c_14,c_568])).

tff(c_582,plain,(
    ! [A_243,B_244] :
      ( u1_struct_0(k8_tmap_1(A_243,B_244)) = u1_struct_0(A_243)
      | ~ v1_pre_topc(k8_tmap_1(A_243,B_244))
      | ~ l1_pre_topc(k8_tmap_1(A_243,B_244))
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243)
      | ~ m1_pre_topc(B_244,A_243)
      | ~ l1_pre_topc(A_243) ) ),
    inference(resolution,[status(thm)],[c_26,c_577])).

tff(c_594,plain,(
    ! [A_249,B_250] :
      ( u1_struct_0(k8_tmap_1(A_249,B_250)) = u1_struct_0(A_249)
      | ~ l1_pre_topc(k8_tmap_1(A_249,B_250))
      | ~ m1_pre_topc(B_250,A_249)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_20,c_582])).

tff(c_599,plain,(
    ! [A_251,B_252] :
      ( u1_struct_0(k8_tmap_1(A_251,B_252)) = u1_struct_0(A_251)
      | ~ m1_pre_topc(B_252,A_251)
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_16,c_594])).

tff(c_40,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_43,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_699,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_43])).

tff(c_706,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_699])).

tff(c_708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_706])).

tff(c_710,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4')
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_759,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_38])).

tff(c_42,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_715,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_715])).

tff(c_722,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_874,plain,(
    ! [A_280,B_281] :
      ( g1_pre_topc(u1_struct_0(A_280),k5_tmap_1(A_280,B_281)) = k6_tmap_1(A_280,B_281)
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_886,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) = k6_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_722,c_874])).

tff(c_900,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) = k6_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_886])).

tff(c_901,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) = k6_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_900])).

tff(c_24,plain,(
    ! [C_35,A_31,D_36,B_32] :
      ( C_35 = A_31
      | g1_pre_topc(C_35,D_36) != g1_pre_topc(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_914,plain,(
    ! [C_35,D_36] :
      ( u1_struct_0('#skF_2') = C_35
      | k6_tmap_1('#skF_2','#skF_4') != g1_pre_topc(C_35,D_36)
      | ~ m1_subset_1(k5_tmap_1('#skF_2','#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_24])).

tff(c_975,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_2','#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_914])).

tff(c_978,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_975])).

tff(c_981,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_722,c_978])).

tff(c_983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_981])).

tff(c_985,plain,(
    m1_subset_1(k5_tmap_1('#skF_2','#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_914])).

tff(c_745,plain,(
    ! [B_254,A_255] :
      ( m1_subset_1(u1_struct_0(B_254),k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ m1_pre_topc(B_254,A_255)
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_751,plain,(
    ! [B_254] :
      ( m1_subset_1(u1_struct_0(B_254),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_254,k8_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_745])).

tff(c_796,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_799,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_796])).

tff(c_802,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_799])).

tff(c_804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_802])).

tff(c_806,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_729,plain,(
    ! [A_253] :
      ( g1_pre_topc(u1_struct_0(A_253),u1_pre_topc(A_253)) = A_253
      | ~ v1_pre_topc(A_253)
      | ~ l1_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_738,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_729])).

tff(c_834,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_738])).

tff(c_835,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_834])).

tff(c_838,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_835])).

tff(c_841,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_838])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_841])).

tff(c_844,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_22,plain,(
    ! [D_36,B_32,C_35,A_31] :
      ( D_36 = B_32
      | g1_pre_topc(C_35,D_36) != g1_pre_topc(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_848,plain,(
    ! [B_32,A_31] :
      ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = B_32
      | k8_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_22])).

tff(c_988,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_4')
    | g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_985,c_848])).

tff(c_999,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_4')
    | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_988])).

tff(c_1000,plain,(
    k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_759,c_999])).

tff(c_845,plain,(
    v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_709,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_821,plain,(
    ! [A_273,B_274] :
      ( m1_subset_1(k5_tmap_1(A_273,B_274),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_273))))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_824,plain,(
    ! [B_274] :
      ( m1_subset_1(k5_tmap_1(k8_tmap_1('#skF_2','#skF_3'),B_274),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_821])).

tff(c_829,plain,(
    ! [B_274] :
      ( m1_subset_1(k5_tmap_1(k8_tmap_1('#skF_2','#skF_3'),B_274),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_710,c_824])).

tff(c_1463,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_829])).

tff(c_1466,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1463])).

tff(c_1469,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_1466])).

tff(c_1471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1469])).

tff(c_1473,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_829])).

tff(c_1329,plain,(
    ! [A_329,B_330] :
      ( k6_tmap_1(A_329,u1_struct_0(B_330)) = k8_tmap_1(A_329,B_330)
      | ~ m1_subset_1(u1_struct_0(B_330),k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_pre_topc(k8_tmap_1(A_329,B_330))
      | ~ v2_pre_topc(k8_tmap_1(A_329,B_330))
      | ~ v1_pre_topc(k8_tmap_1(A_329,B_330))
      | ~ m1_pre_topc(B_330,A_329)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1739,plain,(
    ! [A_367,B_368] :
      ( k6_tmap_1(A_367,u1_struct_0(B_368)) = k8_tmap_1(A_367,B_368)
      | ~ l1_pre_topc(k8_tmap_1(A_367,B_368))
      | ~ v2_pre_topc(k8_tmap_1(A_367,B_368))
      | ~ v1_pre_topc(k8_tmap_1(A_367,B_368))
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367)
      | ~ m1_pre_topc(B_368,A_367)
      | ~ l1_pre_topc(A_367) ) ),
    inference(resolution,[status(thm)],[c_26,c_1329])).

tff(c_1742,plain,
    ( k6_tmap_1('#skF_2',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1473,c_1739])).

tff(c_1748,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_34,c_845,c_806,c_709,c_1742])).

tff(c_1750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1000,c_1748])).

%------------------------------------------------------------------------------
