%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1845+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:31 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  188 (11087 expanded)
%              Number of leaves         :   30 (3521 expanded)
%              Depth                    :   21
%              Number of atoms          :  466 (29687 expanded)
%              Number of equality atoms :   49 (11291 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_pre_topc(A) )
             => v2_pre_topc(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_58,plain,(
    ~ v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    ! [A_18] :
      ( m1_subset_1(u1_pre_topc(A_18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_179,plain,(
    ! [C_54,A_55,D_56,B_57] :
      ( C_54 = A_55
      | g1_pre_topc(C_54,D_56) != g1_pre_topc(A_55,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_197,plain,(
    ! [A_62,B_63] :
      ( u1_struct_0('#skF_5') = A_62
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_179])).

tff(c_201,plain,(
    ! [A_18] :
      ( u1_struct_0(A_18) = u1_struct_0('#skF_5')
      | g1_pre_topc(u1_struct_0(A_18),u1_pre_topc(A_18)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_44,c_197])).

tff(c_231,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_201])).

tff(c_233,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_231])).

tff(c_280,plain,
    ( m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_44])).

tff(c_301,plain,(
    m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_280])).

tff(c_252,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_62])).

tff(c_50,plain,(
    ! [D_25,B_21,C_24,A_20] :
      ( D_25 = B_21
      | g1_pre_topc(C_24,D_25) != g1_pre_topc(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_357,plain,(
    ! [D_25,C_24] :
      ( u1_pre_topc('#skF_5') = D_25
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_24,D_25)
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_50])).

tff(c_367,plain,(
    ! [D_25,C_24] :
      ( u1_pre_topc('#skF_5') = D_25
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_24,D_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_357])).

tff(c_403,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_367])).

tff(c_140,plain,(
    ! [A_42,C_43,B_44] :
      ( m1_subset_1(A_42,C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_143,plain,(
    ! [A_42,A_18] :
      ( m1_subset_1(A_42,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ r2_hidden(A_42,u1_pre_topc(A_18))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_44,c_140])).

tff(c_259,plain,(
    ! [A_42] :
      ( m1_subset_1(A_42,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_42,u1_pre_topc('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_143])).

tff(c_287,plain,(
    ! [A_42] :
      ( m1_subset_1(A_42,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_42,u1_pre_topc('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_259])).

tff(c_419,plain,(
    ! [A_42] :
      ( m1_subset_1(A_42,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_42,u1_pre_topc('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_287])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    ! [A_2] :
      ( r2_hidden(u1_struct_0(A_2),u1_pre_topc(A_2))
      | ~ v2_pre_topc(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_303,plain,(
    ! [A_73] :
      ( r1_tarski('#skF_1'(A_73),u1_pre_topc(A_73))
      | r2_hidden('#skF_3'(A_73),u1_pre_topc(A_73))
      | v2_pre_topc(A_73)
      | ~ r2_hidden(u1_struct_0(A_73),u1_pre_topc(A_73))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_306,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_303])).

tff(c_311,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_306])).

tff(c_312,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_311])).

tff(c_491,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_403,c_312])).

tff(c_492,plain,(
    ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_495,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_492])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_495])).

tff(c_501,plain,(
    r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_535,plain,(
    ! [A_80] :
      ( r1_tarski('#skF_1'(A_80),u1_pre_topc(A_80))
      | m1_subset_1('#skF_2'(A_80),k1_zfmisc_1(u1_struct_0(A_80)))
      | v2_pre_topc(A_80)
      | ~ r2_hidden(u1_struct_0(A_80),u1_pre_topc(A_80))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_540,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_535])).

tff(c_543,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_540])).

tff(c_544,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_543])).

tff(c_550,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_764,plain,(
    ! [A_93] :
      ( m1_subset_1('#skF_1'(A_93),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_93))))
      | r2_hidden('#skF_3'(A_93),u1_pre_topc(A_93))
      | v2_pre_topc(A_93)
      | ~ r2_hidden(u1_struct_0(A_93),u1_pre_topc(A_93))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_778,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_764])).

tff(c_784,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_778])).

tff(c_785,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_784])).

tff(c_786,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_785])).

tff(c_980,plain,(
    ! [A_99] :
      ( m1_subset_1('#skF_1'(A_99),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_99))))
      | m1_subset_1('#skF_3'(A_99),k1_zfmisc_1(u1_struct_0(A_99)))
      | v2_pre_topc(A_99)
      | ~ r2_hidden(u1_struct_0(A_99),u1_pre_topc(A_99))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_997,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_980])).

tff(c_1005,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_233,c_997])).

tff(c_1006,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1005])).

tff(c_1007,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1006])).

tff(c_613,plain,(
    ! [A_90] :
      ( m1_subset_1('#skF_1'(A_90),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_90))))
      | r2_hidden('#skF_2'(A_90),u1_pre_topc(A_90))
      | v2_pre_topc(A_90)
      | ~ r2_hidden(u1_struct_0(A_90),u1_pre_topc(A_90))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_627,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_613])).

tff(c_633,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_627])).

tff(c_634,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_633])).

tff(c_635,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_2864,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_172),B_173,C_174),u1_pre_topc(A_172))
      | ~ r2_hidden(C_174,u1_pre_topc(A_172))
      | ~ r2_hidden(B_173,u1_pre_topc(A_172))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ v2_pre_topc(A_172)
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2487,plain,(
    ! [A_152] :
      ( m1_subset_1('#skF_1'(A_152),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_152))))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_152),'#skF_2'(A_152),'#skF_3'(A_152)),u1_pre_topc(A_152))
      | v2_pre_topc(A_152)
      | ~ r2_hidden(u1_struct_0(A_152),u1_pre_topc(A_152))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2505,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_2487])).

tff(c_2514,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_233,c_2505])).

tff(c_2515,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2514])).

tff(c_2516,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2515])).

tff(c_2871,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2864,c_2516])).

tff(c_2910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_550,c_1007,c_635,c_786,c_2871])).

tff(c_2912,plain,(
    r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2515])).

tff(c_2911,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_2515])).

tff(c_500,plain,
    ( r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_555,plain,(
    r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_54,plain,(
    ! [A_26,B_27] :
      ( k5_setfam_1(A_26,B_27) = k3_tarski(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2932,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2911,c_54])).

tff(c_46,plain,(
    ! [A_19] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_19),u1_pre_topc(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    ! [A_37,B_38] :
      ( l1_pre_topc(g1_pre_topc(A_37,B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    ! [A_39] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_92,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_89])).

tff(c_94,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_92])).

tff(c_68,plain,(
    ! [A_33,B_34] :
      ( v1_pre_topc(g1_pre_topc(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_72,plain,(
    ! [A_18] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_18),u1_pre_topc(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_83,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_72])).

tff(c_87,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_83])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_181,plain,(
    ! [A_1,A_55,B_57] :
      ( u1_struct_0(A_1) = A_55
      | g1_pre_topc(A_55,B_57) != A_1
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_55)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_349,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_4')
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_181])).

tff(c_363,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_4')
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_349])).

tff(c_833,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_363])).

tff(c_835,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_87,c_833])).

tff(c_166,plain,(
    ! [D_50,B_51,C_52,A_53] :
      ( D_50 = B_51
      | g1_pre_topc(C_52,D_50) != g1_pre_topc(A_53,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_168,plain,(
    ! [A_1,B_51,A_53] :
      ( u1_pre_topc(A_1) = B_51
      | g1_pre_topc(A_53,B_51) != A_1
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_53)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_166])).

tff(c_347,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_5')
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_168])).

tff(c_361,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_5')
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_347])).

tff(c_650,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_4')
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_361])).

tff(c_654,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_650])).

tff(c_656,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_87,c_654])).

tff(c_36,plain,(
    ! [A_2,B_11] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_2),B_11),u1_pre_topc(A_2))
      | ~ r1_tarski(B_11,u1_pre_topc(A_2))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ v2_pre_topc(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_860,plain,(
    ! [B_11] :
      ( r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),B_11),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ r1_tarski(B_11,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_36])).

tff(c_907,plain,(
    ! [B_11] :
      ( r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),B_11),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(B_11,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_835,c_656,c_656,c_860])).

tff(c_1584,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_907])).

tff(c_1590,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1584])).

tff(c_1596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_66,c_1590])).

tff(c_1597,plain,(
    ! [B_11] :
      ( r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),B_11),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(B_11,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(splitRight,[status(thm)],[c_907])).

tff(c_2940,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2932,c_1597])).

tff(c_2947,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2911,c_555,c_2940])).

tff(c_2968,plain,(
    ! [A_176] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_176),'#skF_1'(A_176)),u1_pre_topc(A_176))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_176),'#skF_2'(A_176),'#skF_3'(A_176)),u1_pre_topc(A_176))
      | v2_pre_topc(A_176)
      | ~ r2_hidden(u1_struct_0(A_176),u1_pre_topc(A_176))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2983,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_2968])).

tff(c_2992,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_2912,c_233,c_2947,c_2932,c_233,c_403,c_2983])).

tff(c_2994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2992])).

tff(c_2996,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1006])).

tff(c_2999,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(resolution,[status(thm)],[c_419,c_2996])).

tff(c_3006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_2999])).

tff(c_3008,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_785])).

tff(c_3007,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_785])).

tff(c_3020,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3007,c_54])).

tff(c_3030,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3020,c_36])).

tff(c_3034,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_3007,c_555,c_3030])).

tff(c_3112,plain,(
    ! [A_182] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_182),'#skF_1'(A_182)),u1_pre_topc(A_182))
      | r2_hidden('#skF_3'(A_182),u1_pre_topc(A_182))
      | v2_pre_topc(A_182)
      | ~ r2_hidden(u1_struct_0(A_182),u1_pre_topc(A_182))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3122,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_3112])).

tff(c_3130,plain,
    ( r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_3034,c_3020,c_233,c_3122])).

tff(c_3132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3008,c_3130])).

tff(c_3134,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_3133,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_3146,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3133,c_54])).

tff(c_3156,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3146,c_36])).

tff(c_3160,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_3133,c_555,c_3156])).

tff(c_3633,plain,(
    ! [A_205] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_205),'#skF_1'(A_205)),u1_pre_topc(A_205))
      | r2_hidden('#skF_2'(A_205),u1_pre_topc(A_205))
      | v2_pre_topc(A_205)
      | ~ r2_hidden(u1_struct_0(A_205),u1_pre_topc(A_205))
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3646,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_3633])).

tff(c_3656,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_3160,c_3146,c_233,c_3646])).

tff(c_3658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3134,c_3656])).

tff(c_3660,plain,(
    ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_391,plain,(
    ! [A_77] :
      ( r1_tarski('#skF_1'(A_77),u1_pre_topc(A_77))
      | m1_subset_1('#skF_3'(A_77),k1_zfmisc_1(u1_struct_0(A_77)))
      | v2_pre_topc(A_77)
      | ~ r2_hidden(u1_struct_0(A_77),u1_pre_topc(A_77))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_396,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_391])).

tff(c_399,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_233,c_396])).

tff(c_400,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_399])).

tff(c_4037,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_403,c_403,c_400])).

tff(c_4038,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3660,c_4037])).

tff(c_18,plain,(
    ! [A_2] :
      ( r1_tarski('#skF_1'(A_2),u1_pre_topc(A_2))
      | r2_hidden('#skF_2'(A_2),u1_pre_topc(A_2))
      | v2_pre_topc(A_2)
      | ~ r2_hidden(u1_struct_0(A_2),u1_pre_topc(A_2))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_18])).

tff(c_284,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_256])).

tff(c_285,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_284])).

tff(c_3678,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_403,c_403,c_403,c_285])).

tff(c_3679,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_3660,c_3678])).

tff(c_3659,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_6143,plain,(
    ! [A_298,B_299,C_300] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_298),B_299,C_300),u1_pre_topc(A_298))
      | ~ r2_hidden(C_300,u1_pre_topc(A_298))
      | ~ r2_hidden(B_299,u1_pre_topc(A_298))
      | ~ m1_subset_1(C_300,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ v2_pre_topc(A_298)
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5294,plain,(
    ! [A_268] :
      ( r1_tarski('#skF_1'(A_268),u1_pre_topc(A_268))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_268),'#skF_2'(A_268),'#skF_3'(A_268)),u1_pre_topc(A_268))
      | v2_pre_topc(A_268)
      | ~ r2_hidden(u1_struct_0(A_268),u1_pre_topc(A_268))
      | ~ l1_pre_topc(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5312,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_5294])).

tff(c_5321,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_403,c_5312])).

tff(c_5322,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3660,c_5321])).

tff(c_6158,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6143,c_5322])).

tff(c_6191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_550,c_4038,c_3679,c_3659,c_6158])).

tff(c_6193,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_6200,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(resolution,[status(thm)],[c_419,c_6193])).

tff(c_6458,plain,(
    ! [A_312] :
      ( m1_subset_1('#skF_1'(A_312),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_312))))
      | r2_hidden('#skF_2'(A_312),u1_pre_topc(A_312))
      | v2_pre_topc(A_312)
      | ~ r2_hidden(u1_struct_0(A_312),u1_pre_topc(A_312))
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6475,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_6458])).

tff(c_6483,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_6475])).

tff(c_6484,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6200,c_6483])).

tff(c_6192,plain,(
    r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_6504,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6484,c_54])).

tff(c_6513,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6504,c_36])).

tff(c_6517,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_6484,c_6192,c_6513])).

tff(c_6576,plain,(
    ! [A_318] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_318),'#skF_1'(A_318)),u1_pre_topc(A_318))
      | r2_hidden('#skF_2'(A_318),u1_pre_topc(A_318))
      | v2_pre_topc(A_318)
      | ~ r2_hidden(u1_struct_0(A_318),u1_pre_topc(A_318))
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6586,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_6576])).

tff(c_6594,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_501,c_233,c_403,c_403,c_6517,c_6504,c_233,c_6586])).

tff(c_6596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6200,c_6594])).

%------------------------------------------------------------------------------
