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
% DateTime   : Thu Dec  3 10:29:58 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.27s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 143 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   21
%              Number of atoms          :  189 ( 354 expanded)
%              Number of equality atoms :   38 (  61 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_58])).

tff(c_8,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_5') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_8])).

tff(c_12,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),B_44) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_12])).

tff(c_101,plain,(
    ! [A_43] : k1_tarski(A_43) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_97])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_6])).

tff(c_105,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | A_2 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_102,c_105])).

tff(c_44,plain,(
    ! [A_33,B_35] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_33),B_35),A_33)
      | ~ m1_subset_1(B_35,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_14])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_628,plain,(
    ! [C_101,B_102,A_103] :
      ( C_101 = B_102
      | ~ r1_tarski(B_102,C_101)
      | ~ v2_tex_2(C_101,A_103)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v3_tex_2(B_102,A_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_630,plain,(
    ! [A_5,A_103] :
      ( A_5 = '#skF_5'
      | ~ v2_tex_2(A_5,A_103)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v3_tex_2('#skF_5',A_103)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_69,c_628])).

tff(c_778,plain,(
    ! [A_112,A_113] :
      ( A_112 = '#skF_5'
      | ~ v2_tex_2(A_112,A_113)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v3_tex_2('#skF_5',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_630])).

tff(c_8142,plain,(
    ! [A_271,B_272] :
      ( k6_domain_1(u1_struct_0(A_271),B_272) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_271),B_272),A_271)
      | ~ v3_tex_2('#skF_5',A_271)
      | ~ l1_pre_topc(A_271)
      | ~ m1_subset_1(B_272,u1_struct_0(A_271))
      | v1_xboole_0(u1_struct_0(A_271)) ) ),
    inference(resolution,[status(thm)],[c_28,c_778])).

tff(c_8166,plain,(
    ! [A_273,B_274] :
      ( k6_domain_1(u1_struct_0(A_273),B_274) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_273)
      | v1_xboole_0(u1_struct_0(A_273))
      | ~ m1_subset_1(B_274,u1_struct_0(A_273))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_44,c_8142])).

tff(c_9970,plain,(
    ! [A_307] :
      ( k6_domain_1(u1_struct_0(A_307),'#skF_1'(u1_struct_0(A_307))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_307)
      | v1_xboole_0(u1_struct_0(A_307))
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307)
      | u1_struct_0(A_307) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_109,c_8166])).

tff(c_157,plain,(
    ! [A_59,B_60] :
      ( k6_domain_1(A_59,B_60) = k1_tarski(B_60)
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_164,plain,(
    ! [A_2] :
      ( k6_domain_1(A_2,'#skF_1'(A_2)) = k1_tarski('#skF_1'(A_2))
      | v1_xboole_0(A_2)
      | A_2 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_109,c_157])).

tff(c_10020,plain,(
    ! [A_307] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_307))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_307))
      | u1_struct_0(A_307) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_307)
      | v1_xboole_0(u1_struct_0(A_307))
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307)
      | u1_struct_0(A_307) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9970,c_164])).

tff(c_10033,plain,(
    ! [A_307] :
      ( v1_xboole_0(u1_struct_0(A_307))
      | u1_struct_0(A_307) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_307)
      | v1_xboole_0(u1_struct_0(A_307))
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307)
      | u1_struct_0(A_307) = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_10020])).

tff(c_10054,plain,(
    ! [A_309] :
      ( ~ v3_tex_2('#skF_5',A_309)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309)
      | u1_struct_0(A_309) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_309)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10033])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_68,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_4])).

tff(c_10067,plain,(
    ! [A_310] :
      ( ~ v3_tex_2('#skF_5',A_310)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310)
      | u1_struct_0(A_310) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_10054,c_68])).

tff(c_10073,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_10067])).

tff(c_10077,plain,
    ( v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_10073])).

tff(c_10078,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10077])).

tff(c_227,plain,(
    ! [A_70] :
      ( m1_subset_1('#skF_2'(A_70),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_238,plain,(
    ! [A_70] :
      ( v1_xboole_0('#skF_2'(A_70))
      | ~ v1_xboole_0(u1_struct_0(A_70))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_227,c_16])).

tff(c_10162,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10078,c_238])).

tff(c_10236,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_10162])).

tff(c_10237,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10236])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_2'(A_17))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10244,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10237,c_24])).

tff(c_10250,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_10244])).

tff(c_10252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.27  
% 9.27/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.27  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 9.27/3.27  
% 9.27/3.27  %Foreground sorts:
% 9.27/3.27  
% 9.27/3.27  
% 9.27/3.27  %Background operators:
% 9.27/3.27  
% 9.27/3.27  
% 9.27/3.27  %Foreground operators:
% 9.27/3.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.27/3.27  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.27/3.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.27/3.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.27/3.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.27/3.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.27/3.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.27/3.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.27/3.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.27/3.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.27/3.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.27/3.27  tff('#skF_5', type, '#skF_5': $i).
% 9.27/3.27  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 9.27/3.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.27/3.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.27/3.27  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.27/3.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.27/3.27  tff('#skF_4', type, '#skF_4': $i).
% 9.27/3.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.27/3.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.27/3.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.27/3.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.27/3.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.27/3.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.27/3.27  
% 9.27/3.29  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 9.27/3.29  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.27/3.29  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.27/3.29  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 9.27/3.29  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.27/3.29  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.27/3.29  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 9.27/3.29  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 9.27/3.29  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.27/3.29  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.27/3.29  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 9.27/3.29  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.27/3.29  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 9.27/3.29  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.27/3.29  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.27/3.29  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.27/3.29  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.27/3.29  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.27/3.29  tff(c_46, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.27/3.29  tff(c_58, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.27/3.29  tff(c_67, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_58])).
% 9.27/3.29  tff(c_8, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.27/3.29  tff(c_77, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_5')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_8])).
% 9.27/3.29  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.27/3.29  tff(c_97, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), B_44)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_12])).
% 9.27/3.29  tff(c_101, plain, (![A_43]: (k1_tarski(A_43)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_77, c_97])).
% 9.27/3.29  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.27/3.29  tff(c_102, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_6])).
% 9.27/3.29  tff(c_105, plain, (![A_47, B_48]: (m1_subset_1(A_47, B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.27/3.29  tff(c_109, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | A_2='#skF_5')), inference(resolution, [status(thm)], [c_102, c_105])).
% 9.27/3.29  tff(c_44, plain, (![A_33, B_35]: (v2_tex_2(k6_domain_1(u1_struct_0(A_33), B_35), A_33) | ~m1_subset_1(B_35, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.27/3.29  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.27/3.29  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.27/3.29  tff(c_87, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_14])).
% 9.27/3.29  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.27/3.29  tff(c_69, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_10])).
% 9.27/3.29  tff(c_628, plain, (![C_101, B_102, A_103]: (C_101=B_102 | ~r1_tarski(B_102, C_101) | ~v2_tex_2(C_101, A_103) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_103))) | ~v3_tex_2(B_102, A_103) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.27/3.29  tff(c_630, plain, (![A_5, A_103]: (A_5='#skF_5' | ~v2_tex_2(A_5, A_103) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_103))) | ~v3_tex_2('#skF_5', A_103) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_69, c_628])).
% 9.27/3.29  tff(c_778, plain, (![A_112, A_113]: (A_112='#skF_5' | ~v2_tex_2(A_112, A_113) | ~m1_subset_1(A_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~v3_tex_2('#skF_5', A_113) | ~l1_pre_topc(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_630])).
% 9.27/3.29  tff(c_8142, plain, (![A_271, B_272]: (k6_domain_1(u1_struct_0(A_271), B_272)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_271), B_272), A_271) | ~v3_tex_2('#skF_5', A_271) | ~l1_pre_topc(A_271) | ~m1_subset_1(B_272, u1_struct_0(A_271)) | v1_xboole_0(u1_struct_0(A_271)))), inference(resolution, [status(thm)], [c_28, c_778])).
% 9.27/3.29  tff(c_8166, plain, (![A_273, B_274]: (k6_domain_1(u1_struct_0(A_273), B_274)='#skF_5' | ~v3_tex_2('#skF_5', A_273) | v1_xboole_0(u1_struct_0(A_273)) | ~m1_subset_1(B_274, u1_struct_0(A_273)) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_44, c_8142])).
% 9.27/3.29  tff(c_9970, plain, (![A_307]: (k6_domain_1(u1_struct_0(A_307), '#skF_1'(u1_struct_0(A_307)))='#skF_5' | ~v3_tex_2('#skF_5', A_307) | v1_xboole_0(u1_struct_0(A_307)) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | v2_struct_0(A_307) | u1_struct_0(A_307)='#skF_5')), inference(resolution, [status(thm)], [c_109, c_8166])).
% 9.27/3.29  tff(c_157, plain, (![A_59, B_60]: (k6_domain_1(A_59, B_60)=k1_tarski(B_60) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.29  tff(c_164, plain, (![A_2]: (k6_domain_1(A_2, '#skF_1'(A_2))=k1_tarski('#skF_1'(A_2)) | v1_xboole_0(A_2) | A_2='#skF_5')), inference(resolution, [status(thm)], [c_109, c_157])).
% 9.27/3.29  tff(c_10020, plain, (![A_307]: (k1_tarski('#skF_1'(u1_struct_0(A_307)))='#skF_5' | v1_xboole_0(u1_struct_0(A_307)) | u1_struct_0(A_307)='#skF_5' | ~v3_tex_2('#skF_5', A_307) | v1_xboole_0(u1_struct_0(A_307)) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | v2_struct_0(A_307) | u1_struct_0(A_307)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9970, c_164])).
% 9.27/3.29  tff(c_10033, plain, (![A_307]: (v1_xboole_0(u1_struct_0(A_307)) | u1_struct_0(A_307)='#skF_5' | ~v3_tex_2('#skF_5', A_307) | v1_xboole_0(u1_struct_0(A_307)) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | v2_struct_0(A_307) | u1_struct_0(A_307)='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_101, c_10020])).
% 9.27/3.29  tff(c_10054, plain, (![A_309]: (~v3_tex_2('#skF_5', A_309) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309) | u1_struct_0(A_309)='#skF_5' | v1_xboole_0(u1_struct_0(A_309)))), inference(factorization, [status(thm), theory('equality')], [c_10033])).
% 9.27/3.29  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.27/3.29  tff(c_68, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_4])).
% 9.27/3.29  tff(c_10067, plain, (![A_310]: (~v3_tex_2('#skF_5', A_310) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310) | u1_struct_0(A_310)='#skF_5')), inference(resolution, [status(thm)], [c_10054, c_68])).
% 9.27/3.29  tff(c_10073, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_10067])).
% 9.27/3.29  tff(c_10077, plain, (v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_10073])).
% 9.27/3.29  tff(c_10078, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_56, c_10077])).
% 9.27/3.29  tff(c_227, plain, (![A_70]: (m1_subset_1('#skF_2'(A_70), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.27/3.29  tff(c_16, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.27/3.29  tff(c_238, plain, (![A_70]: (v1_xboole_0('#skF_2'(A_70)) | ~v1_xboole_0(u1_struct_0(A_70)) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(resolution, [status(thm)], [c_227, c_16])).
% 9.27/3.29  tff(c_10162, plain, (v1_xboole_0('#skF_2'('#skF_4')) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10078, c_238])).
% 9.27/3.29  tff(c_10236, plain, (v1_xboole_0('#skF_2'('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_10162])).
% 9.27/3.29  tff(c_10237, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_10236])).
% 9.27/3.29  tff(c_24, plain, (![A_17]: (~v1_xboole_0('#skF_2'(A_17)) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.27/3.29  tff(c_10244, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_10237, c_24])).
% 9.27/3.29  tff(c_10250, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_10244])).
% 9.27/3.29  tff(c_10252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_10250])).
% 9.27/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.29  
% 9.27/3.29  Inference rules
% 9.27/3.29  ----------------------
% 9.27/3.29  #Ref     : 0
% 9.27/3.29  #Sup     : 2297
% 9.27/3.29  #Fact    : 2
% 9.27/3.29  #Define  : 0
% 9.27/3.29  #Split   : 8
% 9.27/3.29  #Chain   : 0
% 9.27/3.29  #Close   : 0
% 9.27/3.29  
% 9.27/3.29  Ordering : KBO
% 9.27/3.29  
% 9.27/3.29  Simplification rules
% 9.27/3.29  ----------------------
% 9.27/3.29  #Subsume      : 462
% 9.27/3.29  #Demod        : 2644
% 9.27/3.29  #Tautology    : 908
% 9.27/3.29  #SimpNegUnit  : 770
% 9.27/3.29  #BackRed      : 10
% 9.27/3.29  
% 9.27/3.29  #Partial instantiations: 0
% 9.27/3.29  #Strategies tried      : 1
% 9.27/3.29  
% 9.27/3.29  Timing (in seconds)
% 9.27/3.29  ----------------------
% 9.27/3.29  Preprocessing        : 0.33
% 9.27/3.29  Parsing              : 0.17
% 9.27/3.29  CNF conversion       : 0.02
% 9.27/3.29  Main loop            : 2.18
% 9.27/3.29  Inferencing          : 0.58
% 9.27/3.29  Reduction            : 0.68
% 9.27/3.29  Demodulation         : 0.46
% 9.27/3.29  BG Simplification    : 0.07
% 9.27/3.29  Subsumption          : 0.73
% 9.27/3.29  Abstraction          : 0.10
% 9.27/3.29  MUC search           : 0.00
% 9.27/3.29  Cooper               : 0.00
% 9.27/3.29  Total                : 2.54
% 9.27/3.29  Index Insertion      : 0.00
% 9.27/3.29  Index Deletion       : 0.00
% 9.27/3.29  Index Matching       : 0.00
% 9.27/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
