%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:56 EST 2020

% Result     : Theorem 10.94s
% Output     : CNFRefutation 11.15s
% Verified   : 
% Statistics : Number of formulae       :  206 (12887 expanded)
%              Number of leaves         :   41 (4446 expanded)
%              Depth                    :   20
%              Number of atoms          :  391 (30978 expanded)
%              Number of equality atoms :   87 (5975 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_146,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_102,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_108,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_102])).

tff(c_112,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_108])).

tff(c_44,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    ! [B_46,A_40] :
      ( u1_struct_0(B_46) = '#skF_1'(A_40,B_46)
      | v1_tex_2(B_46,A_40)
      | ~ m1_pre_topc(B_46,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    ! [B_51] :
      ( ~ v1_subset_1(B_51,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_71,plain,(
    ! [B_51] : ~ v1_subset_1(B_51,B_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_58])).

tff(c_17310,plain,(
    ! [B_592,A_593] :
      ( v1_subset_1(u1_struct_0(B_592),u1_struct_0(A_593))
      | ~ m1_subset_1(u1_struct_0(B_592),k1_zfmisc_1(u1_struct_0(A_593)))
      | ~ v1_tex_2(B_592,A_593)
      | ~ m1_pre_topc(B_592,A_593)
      | ~ l1_pre_topc(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_17344,plain,(
    ! [B_592] :
      ( v1_subset_1(u1_struct_0(B_592),u1_struct_0(B_592))
      | ~ v1_tex_2(B_592,B_592)
      | ~ m1_pre_topc(B_592,B_592)
      | ~ l1_pre_topc(B_592) ) ),
    inference(resolution,[status(thm)],[c_69,c_17310])).

tff(c_17363,plain,(
    ! [B_594] :
      ( ~ v1_tex_2(B_594,B_594)
      | ~ m1_pre_topc(B_594,B_594)
      | ~ l1_pre_topc(B_594) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_17344])).

tff(c_17369,plain,(
    ! [A_595] :
      ( u1_struct_0(A_595) = '#skF_1'(A_595,A_595)
      | ~ m1_pre_topc(A_595,A_595)
      | ~ l1_pre_topc(A_595) ) ),
    inference(resolution,[status(thm)],[c_52,c_17363])).

tff(c_17412,plain,(
    ! [A_596] :
      ( u1_struct_0(A_596) = '#skF_1'(A_596,A_596)
      | ~ l1_pre_topc(A_596) ) ),
    inference(resolution,[status(thm)],[c_44,c_17369])).

tff(c_17435,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_17412])).

tff(c_24,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    ! [A_16] :
      ( u1_struct_0(A_16) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_123,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_91])).

tff(c_16423,plain,(
    ! [B_559,A_560] :
      ( u1_struct_0(B_559) = '#skF_1'(A_560,B_559)
      | v1_tex_2(B_559,A_560)
      | ~ m1_pre_topc(B_559,A_560)
      | ~ l1_pre_topc(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,(
    ~ v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_16426,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16423,c_64])).

tff(c_16429,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_123,c_16426])).

tff(c_16457,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_123])).

tff(c_17455,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17435,c_16457])).

tff(c_28,plain,(
    ! [A_20] :
      ( m1_subset_1(u1_pre_topc(A_20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20))))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_183,plain,(
    ! [A_71,B_72] :
      ( v1_pre_topc(g1_pre_topc(A_71,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_199,plain,(
    ! [A_20] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_20),u1_pre_topc(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_28,c_183])).

tff(c_16483,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16457,c_199])).

tff(c_16498,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_16483])).

tff(c_17583,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16498])).

tff(c_137,plain,(
    ! [A_67] :
      ( m1_subset_1(u1_pre_topc(A_67),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67))))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_143,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_137])).

tff(c_149,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_143])).

tff(c_160,plain,(
    ! [A_68,B_69] :
      ( l1_pre_topc(g1_pre_topc(A_68,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_175,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_149,c_160])).

tff(c_16149,plain,(
    ! [B_546,A_547] :
      ( m1_pre_topc(B_546,A_547)
      | ~ m1_pre_topc(B_546,g1_pre_topc(u1_struct_0(A_547),u1_pre_topc(A_547)))
      | ~ l1_pre_topc(A_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16169,plain,(
    ! [B_546] :
      ( m1_pre_topc(B_546,'#skF_3')
      | ~ m1_pre_topc(B_546,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_16149])).

tff(c_16183,plain,(
    ! [B_548] :
      ( m1_pre_topc(B_548,'#skF_3')
      | ~ m1_pre_topc(B_548,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_16169])).

tff(c_16195,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_44,c_16183])).

tff(c_16204,plain,(
    m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_16195])).

tff(c_16437,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_16204])).

tff(c_17577,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16437])).

tff(c_176,plain,(
    ! [A_20] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_20),u1_pre_topc(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_28,c_160])).

tff(c_16480,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16457,c_176])).

tff(c_16496,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_16480])).

tff(c_17584,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16496])).

tff(c_16568,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) = k2_struct_0(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16496,c_91])).

tff(c_18895,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_17455,c_16568])).

tff(c_16456,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_149])).

tff(c_17578,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_3','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16456])).

tff(c_12,plain,(
    ! [A_5] :
      ( g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)) = A_5
      | ~ v1_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16573,plain,(
    ! [C_562,A_563,D_564,B_565] :
      ( C_562 = A_563
      | g1_pre_topc(C_562,D_564) != g1_pre_topc(A_563,B_565)
      | ~ m1_subset_1(B_565,k1_zfmisc_1(k1_zfmisc_1(A_563))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16575,plain,(
    ! [A_5,A_563,B_565] :
      ( u1_struct_0(A_5) = A_563
      | g1_pre_topc(A_563,B_565) != A_5
      | ~ m1_subset_1(B_565,k1_zfmisc_1(k1_zfmisc_1(A_563)))
      | ~ v1_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_16573])).

tff(c_19407,plain,(
    ! [A_663,B_664] :
      ( u1_struct_0(g1_pre_topc(A_663,B_664)) = A_663
      | ~ m1_subset_1(B_664,k1_zfmisc_1(k1_zfmisc_1(A_663)))
      | ~ v1_pre_topc(g1_pre_topc(A_663,B_664))
      | ~ l1_pre_topc(g1_pre_topc(A_663,B_664)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16575])).

tff(c_19413,plain,
    ( u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_17578,c_19407])).

tff(c_19429,plain,(
    k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17584,c_17583,c_18895,c_19413])).

tff(c_14,plain,(
    ! [A_6,C_12] :
      ( k1_pre_topc(A_6,k2_struct_0(C_12)) = C_12
      | ~ m1_pre_topc(C_12,A_6)
      | ~ v1_pre_topc(C_12)
      | ~ m1_subset_1(k2_struct_0(C_12),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17465,plain,(
    ! [C_12] :
      ( k1_pre_topc('#skF_3',k2_struct_0(C_12)) = C_12
      | ~ m1_pre_topc(C_12,'#skF_3')
      | ~ v1_pre_topc(C_12)
      | ~ m1_subset_1(k2_struct_0(C_12),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17435,c_14])).

tff(c_21609,plain,(
    ! [C_713] :
      ( k1_pre_topc('#skF_3',k2_struct_0(C_713)) = C_713
      | ~ m1_pre_topc(C_713,'#skF_3')
      | ~ v1_pre_topc(C_713)
      | ~ m1_subset_1(k2_struct_0(C_713),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_17465])).

tff(c_21615,plain,
    ( k1_pre_topc('#skF_3',k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))) = g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19429,c_21609])).

tff(c_21631,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')) = k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_17583,c_17577,c_19429,c_21615])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1574,plain,(
    ! [B_144,A_145] :
      ( v1_subset_1(u1_struct_0(B_144),u1_struct_0(A_145))
      | ~ m1_subset_1(u1_struct_0(B_144),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ v1_tex_2(B_144,A_145)
      | ~ m1_pre_topc(B_144,A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1602,plain,(
    ! [B_144] :
      ( v1_subset_1(u1_struct_0(B_144),u1_struct_0(B_144))
      | ~ v1_tex_2(B_144,B_144)
      | ~ m1_pre_topc(B_144,B_144)
      | ~ l1_pre_topc(B_144) ) ),
    inference(resolution,[status(thm)],[c_69,c_1574])).

tff(c_1618,plain,(
    ! [B_146] :
      ( ~ v1_tex_2(B_146,B_146)
      | ~ m1_pre_topc(B_146,B_146)
      | ~ l1_pre_topc(B_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1602])).

tff(c_1624,plain,(
    ! [A_147] :
      ( u1_struct_0(A_147) = '#skF_1'(A_147,A_147)
      | ~ m1_pre_topc(A_147,A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(resolution,[status(thm)],[c_52,c_1618])).

tff(c_1667,plain,(
    ! [A_148] :
      ( u1_struct_0(A_148) = '#skF_1'(A_148,A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_44,c_1624])).

tff(c_1690,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1667])).

tff(c_1689,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_1667])).

tff(c_1027,plain,(
    ! [B_117,A_118] :
      ( u1_struct_0(B_117) = '#skF_1'(A_118,B_117)
      | v1_tex_2(B_117,A_118)
      | ~ m1_pre_topc(B_117,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1030,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1027,c_64])).

tff(c_1033,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_123,c_1030])).

tff(c_1053,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_123])).

tff(c_1791,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1689,c_1053])).

tff(c_50,plain,(
    ! [A_40,B_46] :
      ( ~ v1_subset_1('#skF_1'(A_40,B_46),u1_struct_0(A_40))
      | v1_tex_2(B_46,A_40)
      | ~ m1_pre_topc(B_46,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1954,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1791,c_50])).

tff(c_1964,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_2','#skF_2'))
    | v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1690,c_1954])).

tff(c_1965,plain,(
    ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_2','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1964])).

tff(c_1339,plain,(
    ! [A_128,B_129] :
      ( m1_subset_1('#skF_1'(A_128,B_129),k1_zfmisc_1(u1_struct_0(A_128)))
      | v1_tex_2(B_129,A_128)
      | ~ m1_pre_topc(B_129,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    ! [B_51,A_50] :
      ( v1_subset_1(B_51,A_50)
      | B_51 = A_50
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2507,plain,(
    ! [A_180,B_181] :
      ( v1_subset_1('#skF_1'(A_180,B_181),u1_struct_0(A_180))
      | u1_struct_0(A_180) = '#skF_1'(A_180,B_181)
      | v1_tex_2(B_181,A_180)
      | ~ m1_pre_topc(B_181,A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_1339,c_56])).

tff(c_2513,plain,
    ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_3')
    | v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1791,c_2507])).

tff(c_2525,plain,
    ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_2','#skF_2'))
    | '#skF_1'('#skF_2','#skF_2') = '#skF_1'('#skF_3','#skF_3')
    | v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1791,c_1690,c_1690,c_2513])).

tff(c_2526,plain,(
    '#skF_1'('#skF_2','#skF_2') = '#skF_1'('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1965,c_2525])).

tff(c_92,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_96,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_92])).

tff(c_1691,plain,(
    k2_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_96])).

tff(c_236,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(u1_struct_0(B_76),u1_struct_0(A_77))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_250,plain,(
    ! [B_76] :
      ( r1_tarski(u1_struct_0(B_76),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_76,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_236])).

tff(c_292,plain,(
    ! [B_80] :
      ( r1_tarski(u1_struct_0(B_80),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_80,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_250])).

tff(c_297,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_292])).

tff(c_303,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_297])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_307,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_303,c_2])).

tff(c_311,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_1047,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_311])).

tff(c_1896,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_2'),'#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_1047])).

tff(c_2188,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_2'),'#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_1896])).

tff(c_2544,plain,(
    ~ r1_tarski('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2526,c_2188])).

tff(c_2555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2544])).

tff(c_2556,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_60,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_97,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60])).

tff(c_136,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_97])).

tff(c_2563,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) != g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_136])).

tff(c_16445,plain,(
    g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) != g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_16429,c_2563])).

tff(c_17576,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) != g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_17455,c_16445])).

tff(c_21648,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) != k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21631,c_17576])).

tff(c_21653,plain,(
    v1_pre_topc(k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21631,c_17583])).

tff(c_2564,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_96])).

tff(c_16451,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_2564])).

tff(c_17589,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16451])).

tff(c_38,plain,(
    ! [A_30,B_32] :
      ( m1_pre_topc(A_30,g1_pre_topc(u1_struct_0(B_32),u1_pre_topc(B_32)))
      | ~ m1_pre_topc(A_30,B_32)
      | ~ l1_pre_topc(B_32)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_17644,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_30,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17589,c_38])).

tff(c_17683,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_30,'#skF_2')
      | ~ l1_pre_topc(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_17644])).

tff(c_17590,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16429])).

tff(c_146,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_137])).

tff(c_151,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_146])).

tff(c_174,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_151,c_160])).

tff(c_2560,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_174])).

tff(c_8007,plain,(
    ! [B_354,A_355] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_354),u1_pre_topc(B_354)),A_355)
      | ~ m1_pre_topc(B_354,A_355)
      | ~ l1_pre_topc(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16269,plain,(
    ! [A_555] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_555)
      | ~ m1_pre_topc('#skF_3',A_555)
      | ~ l1_pre_topc(A_555) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_8007])).

tff(c_16163,plain,(
    ! [B_546] :
      ( m1_pre_topc(B_546,'#skF_2')
      | ~ m1_pre_topc(B_546,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2564,c_16149])).

tff(c_16179,plain,(
    ! [B_546] :
      ( m1_pre_topc(B_546,'#skF_2')
      | ~ m1_pre_topc(B_546,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16163])).

tff(c_16273,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ m1_pre_topc('#skF_3',g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16269,c_16179])).

tff(c_16291,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ m1_pre_topc('#skF_3',g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_16273])).

tff(c_21203,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ m1_pre_topc('#skF_3',g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17590,c_17590,c_16291])).

tff(c_21204,plain,(
    ~ m1_pre_topc('#skF_3',g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_21203])).

tff(c_21207,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_17683,c_21204])).

tff(c_21211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_62,c_21207])).

tff(c_21212,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_21203])).

tff(c_21638,plain,(
    m1_pre_topc(k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21631,c_21212])).

tff(c_21642,plain,(
    k2_struct_0(k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21631,c_19429])).

tff(c_17103,plain,(
    ! [A_583,C_584] :
      ( k1_pre_topc(A_583,k2_struct_0(C_584)) = C_584
      | ~ m1_pre_topc(C_584,A_583)
      | ~ v1_pre_topc(C_584)
      | ~ m1_subset_1(k2_struct_0(C_584),k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ l1_pre_topc(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17115,plain,(
    ! [C_584] :
      ( k1_pre_topc('#skF_2',k2_struct_0(C_584)) = C_584
      | ~ m1_pre_topc(C_584,'#skF_2')
      | ~ v1_pre_topc(C_584)
      | ~ m1_subset_1(k2_struct_0(C_584),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16451,c_17103])).

tff(c_17131,plain,(
    ! [C_584] :
      ( k1_pre_topc('#skF_2',k2_struct_0(C_584)) = C_584
      | ~ m1_pre_topc(C_584,'#skF_2')
      | ~ v1_pre_topc(C_584)
      | ~ m1_subset_1(k2_struct_0(C_584),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_17115])).

tff(c_22676,plain,(
    ! [C_718] :
      ( k1_pre_topc('#skF_2',k2_struct_0(C_718)) = C_718
      | ~ m1_pre_topc(C_718,'#skF_2')
      | ~ v1_pre_topc(C_718)
      | ~ m1_subset_1(k2_struct_0(C_718),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_17131])).

tff(c_22679,plain,
    ( k1_pre_topc('#skF_2',k2_struct_0(k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')))) = k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')),'#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_21642,c_22676])).

tff(c_22696,plain,(
    k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')) = k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_21653,c_21638,c_21642,c_22679])).

tff(c_197,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_151,c_183])).

tff(c_2561,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_197])).

tff(c_16448,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_2561])).

tff(c_17581,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16448])).

tff(c_16449,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_2560])).

tff(c_17579,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16449])).

tff(c_17792,plain,(
    ! [A_601] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_601),u1_pre_topc(A_601)),A_601)
      | ~ l1_pre_topc(A_601)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_601),u1_pre_topc(A_601))) ) ),
    inference(resolution,[status(thm)],[c_44,c_16149])).

tff(c_17806,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17589,c_17792])).

tff(c_17821,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17579,c_17589,c_66,c_17806])).

tff(c_209,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k2_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_174,c_91])).

tff(c_16352,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) = k2_struct_0(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_2556,c_209])).

tff(c_16431,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))) = k2_struct_0(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_16429,c_16352])).

tff(c_19152,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_17455,c_16431])).

tff(c_2562,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_151])).

tff(c_16447,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_2562])).

tff(c_17575,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_3','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17455,c_16447])).

tff(c_19410,plain,
    ( u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = '#skF_1'('#skF_3','#skF_3')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_17575,c_19407])).

tff(c_19426,plain,(
    k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17579,c_17581,c_19152,c_19410])).

tff(c_22682,plain,
    ( k1_pre_topc('#skF_2',k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))) = g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19426,c_22676])).

tff(c_22698,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) = k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_17581,c_17821,c_19426,c_22682])).

tff(c_22871,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) = k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22696,c_22698])).

tff(c_22872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21648,c_22871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.94/4.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/4.54  
% 10.94/4.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/4.55  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 10.94/4.55  
% 10.94/4.55  %Foreground sorts:
% 10.94/4.55  
% 10.94/4.55  
% 10.94/4.55  %Background operators:
% 10.94/4.55  
% 10.94/4.55  
% 10.94/4.55  %Foreground operators:
% 10.94/4.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.94/4.55  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 10.94/4.55  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.94/4.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.94/4.55  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 10.94/4.55  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 10.94/4.55  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 10.94/4.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.94/4.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.94/4.55  tff('#skF_2', type, '#skF_2': $i).
% 10.94/4.55  tff('#skF_3', type, '#skF_3': $i).
% 10.94/4.55  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.94/4.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.94/4.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.94/4.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.94/4.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.94/4.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.94/4.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.94/4.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.94/4.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.94/4.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.94/4.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.94/4.55  
% 11.15/4.57  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.15/4.57  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.15/4.57  tff(f_160, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_tex_2(B, A) & m1_pre_topc(B, A)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tex_2)).
% 11.15/4.57  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.15/4.57  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 11.15/4.57  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 11.15/4.57  tff(f_146, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 11.15/4.57  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.15/4.57  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 11.15/4.57  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 11.15/4.57  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 11.15/4.57  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 11.15/4.57  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 11.15/4.57  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 11.15/4.57  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 11.15/4.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.15/4.57  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 11.15/4.57  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 11.15/4.57  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 11.15/4.57  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.15/4.57  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.15/4.57  tff(c_69, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 11.15/4.57  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.15/4.57  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.15/4.57  tff(c_102, plain, (![B_61, A_62]: (l1_pre_topc(B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.15/4.57  tff(c_108, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_102])).
% 11.15/4.57  tff(c_112, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_108])).
% 11.15/4.57  tff(c_44, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.15/4.57  tff(c_52, plain, (![B_46, A_40]: (u1_struct_0(B_46)='#skF_1'(A_40, B_46) | v1_tex_2(B_46, A_40) | ~m1_pre_topc(B_46, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.15/4.57  tff(c_58, plain, (![B_51]: (~v1_subset_1(B_51, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.15/4.57  tff(c_71, plain, (![B_51]: (~v1_subset_1(B_51, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_58])).
% 11.15/4.57  tff(c_17310, plain, (![B_592, A_593]: (v1_subset_1(u1_struct_0(B_592), u1_struct_0(A_593)) | ~m1_subset_1(u1_struct_0(B_592), k1_zfmisc_1(u1_struct_0(A_593))) | ~v1_tex_2(B_592, A_593) | ~m1_pre_topc(B_592, A_593) | ~l1_pre_topc(A_593))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.15/4.57  tff(c_17344, plain, (![B_592]: (v1_subset_1(u1_struct_0(B_592), u1_struct_0(B_592)) | ~v1_tex_2(B_592, B_592) | ~m1_pre_topc(B_592, B_592) | ~l1_pre_topc(B_592))), inference(resolution, [status(thm)], [c_69, c_17310])).
% 11.15/4.57  tff(c_17363, plain, (![B_594]: (~v1_tex_2(B_594, B_594) | ~m1_pre_topc(B_594, B_594) | ~l1_pre_topc(B_594))), inference(negUnitSimplification, [status(thm)], [c_71, c_17344])).
% 11.15/4.57  tff(c_17369, plain, (![A_595]: (u1_struct_0(A_595)='#skF_1'(A_595, A_595) | ~m1_pre_topc(A_595, A_595) | ~l1_pre_topc(A_595))), inference(resolution, [status(thm)], [c_52, c_17363])).
% 11.15/4.57  tff(c_17412, plain, (![A_596]: (u1_struct_0(A_596)='#skF_1'(A_596, A_596) | ~l1_pre_topc(A_596))), inference(resolution, [status(thm)], [c_44, c_17369])).
% 11.15/4.57  tff(c_17435, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_112, c_17412])).
% 11.15/4.57  tff(c_24, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.15/4.57  tff(c_87, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.15/4.57  tff(c_91, plain, (![A_16]: (u1_struct_0(A_16)=k2_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_24, c_87])).
% 11.15/4.57  tff(c_123, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_112, c_91])).
% 11.15/4.57  tff(c_16423, plain, (![B_559, A_560]: (u1_struct_0(B_559)='#skF_1'(A_560, B_559) | v1_tex_2(B_559, A_560) | ~m1_pre_topc(B_559, A_560) | ~l1_pre_topc(A_560))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.15/4.57  tff(c_64, plain, (~v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.15/4.57  tff(c_16426, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16423, c_64])).
% 11.15/4.57  tff(c_16429, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_123, c_16426])).
% 11.15/4.57  tff(c_16457, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_123])).
% 11.15/4.57  tff(c_17455, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17435, c_16457])).
% 11.15/4.57  tff(c_28, plain, (![A_20]: (m1_subset_1(u1_pre_topc(A_20), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20)))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.15/4.57  tff(c_183, plain, (![A_71, B_72]: (v1_pre_topc(g1_pre_topc(A_71, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.15/4.57  tff(c_199, plain, (![A_20]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_20), u1_pre_topc(A_20))) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_28, c_183])).
% 11.15/4.57  tff(c_16483, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16457, c_199])).
% 11.15/4.57  tff(c_16498, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_16483])).
% 11.15/4.57  tff(c_17583, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16498])).
% 11.15/4.57  tff(c_137, plain, (![A_67]: (m1_subset_1(u1_pre_topc(A_67), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67)))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.15/4.57  tff(c_143, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_137])).
% 11.15/4.57  tff(c_149, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_143])).
% 11.15/4.57  tff(c_160, plain, (![A_68, B_69]: (l1_pre_topc(g1_pre_topc(A_68, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.15/4.57  tff(c_175, plain, (l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_149, c_160])).
% 11.15/4.57  tff(c_16149, plain, (![B_546, A_547]: (m1_pre_topc(B_546, A_547) | ~m1_pre_topc(B_546, g1_pre_topc(u1_struct_0(A_547), u1_pre_topc(A_547))) | ~l1_pre_topc(A_547))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.15/4.57  tff(c_16169, plain, (![B_546]: (m1_pre_topc(B_546, '#skF_3') | ~m1_pre_topc(B_546, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_16149])).
% 11.15/4.57  tff(c_16183, plain, (![B_548]: (m1_pre_topc(B_548, '#skF_3') | ~m1_pre_topc(B_548, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_16169])).
% 11.15/4.57  tff(c_16195, plain, (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_16183])).
% 11.15/4.57  tff(c_16204, plain, (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_16195])).
% 11.15/4.57  tff(c_16437, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_16204])).
% 11.15/4.57  tff(c_17577, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16437])).
% 11.15/4.57  tff(c_176, plain, (![A_20]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_20), u1_pre_topc(A_20))) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_28, c_160])).
% 11.15/4.57  tff(c_16480, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16457, c_176])).
% 11.15/4.57  tff(c_16496, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_16480])).
% 11.15/4.57  tff(c_17584, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16496])).
% 11.15/4.57  tff(c_16568, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))=k2_struct_0(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_16496, c_91])).
% 11.15/4.57  tff(c_18895, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))=k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_17455, c_16568])).
% 11.15/4.57  tff(c_16456, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_149])).
% 11.15/4.57  tff(c_17578, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16456])).
% 11.15/4.57  tff(c_12, plain, (![A_5]: (g1_pre_topc(u1_struct_0(A_5), u1_pre_topc(A_5))=A_5 | ~v1_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.15/4.57  tff(c_16573, plain, (![C_562, A_563, D_564, B_565]: (C_562=A_563 | g1_pre_topc(C_562, D_564)!=g1_pre_topc(A_563, B_565) | ~m1_subset_1(B_565, k1_zfmisc_1(k1_zfmisc_1(A_563))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.15/4.57  tff(c_16575, plain, (![A_5, A_563, B_565]: (u1_struct_0(A_5)=A_563 | g1_pre_topc(A_563, B_565)!=A_5 | ~m1_subset_1(B_565, k1_zfmisc_1(k1_zfmisc_1(A_563))) | ~v1_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_16573])).
% 11.15/4.57  tff(c_19407, plain, (![A_663, B_664]: (u1_struct_0(g1_pre_topc(A_663, B_664))=A_663 | ~m1_subset_1(B_664, k1_zfmisc_1(k1_zfmisc_1(A_663))) | ~v1_pre_topc(g1_pre_topc(A_663, B_664)) | ~l1_pre_topc(g1_pre_topc(A_663, B_664)))), inference(reflexivity, [status(thm), theory('equality')], [c_16575])).
% 11.15/4.57  tff(c_19413, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_17578, c_19407])).
% 11.15/4.57  tff(c_19429, plain, (k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17584, c_17583, c_18895, c_19413])).
% 11.15/4.57  tff(c_14, plain, (![A_6, C_12]: (k1_pre_topc(A_6, k2_struct_0(C_12))=C_12 | ~m1_pre_topc(C_12, A_6) | ~v1_pre_topc(C_12) | ~m1_subset_1(k2_struct_0(C_12), k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.15/4.57  tff(c_17465, plain, (![C_12]: (k1_pre_topc('#skF_3', k2_struct_0(C_12))=C_12 | ~m1_pre_topc(C_12, '#skF_3') | ~v1_pre_topc(C_12) | ~m1_subset_1(k2_struct_0(C_12), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_17435, c_14])).
% 11.15/4.57  tff(c_21609, plain, (![C_713]: (k1_pre_topc('#skF_3', k2_struct_0(C_713))=C_713 | ~m1_pre_topc(C_713, '#skF_3') | ~v1_pre_topc(C_713) | ~m1_subset_1(k2_struct_0(C_713), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_17465])).
% 11.15/4.57  tff(c_21615, plain, (k1_pre_topc('#skF_3', k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))))=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_19429, c_21609])).
% 11.15/4.57  tff(c_21631, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_17583, c_17577, c_19429, c_21615])).
% 11.15/4.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.15/4.57  tff(c_1574, plain, (![B_144, A_145]: (v1_subset_1(u1_struct_0(B_144), u1_struct_0(A_145)) | ~m1_subset_1(u1_struct_0(B_144), k1_zfmisc_1(u1_struct_0(A_145))) | ~v1_tex_2(B_144, A_145) | ~m1_pre_topc(B_144, A_145) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.15/4.57  tff(c_1602, plain, (![B_144]: (v1_subset_1(u1_struct_0(B_144), u1_struct_0(B_144)) | ~v1_tex_2(B_144, B_144) | ~m1_pre_topc(B_144, B_144) | ~l1_pre_topc(B_144))), inference(resolution, [status(thm)], [c_69, c_1574])).
% 11.15/4.57  tff(c_1618, plain, (![B_146]: (~v1_tex_2(B_146, B_146) | ~m1_pre_topc(B_146, B_146) | ~l1_pre_topc(B_146))), inference(negUnitSimplification, [status(thm)], [c_71, c_1602])).
% 11.15/4.57  tff(c_1624, plain, (![A_147]: (u1_struct_0(A_147)='#skF_1'(A_147, A_147) | ~m1_pre_topc(A_147, A_147) | ~l1_pre_topc(A_147))), inference(resolution, [status(thm)], [c_52, c_1618])).
% 11.15/4.57  tff(c_1667, plain, (![A_148]: (u1_struct_0(A_148)='#skF_1'(A_148, A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_44, c_1624])).
% 11.15/4.57  tff(c_1690, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1667])).
% 11.15/4.57  tff(c_1689, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_112, c_1667])).
% 11.15/4.57  tff(c_1027, plain, (![B_117, A_118]: (u1_struct_0(B_117)='#skF_1'(A_118, B_117) | v1_tex_2(B_117, A_118) | ~m1_pre_topc(B_117, A_118) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.15/4.57  tff(c_1030, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1027, c_64])).
% 11.15/4.57  tff(c_1033, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_123, c_1030])).
% 11.15/4.57  tff(c_1053, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_123])).
% 11.15/4.57  tff(c_1791, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1689, c_1053])).
% 11.15/4.57  tff(c_50, plain, (![A_40, B_46]: (~v1_subset_1('#skF_1'(A_40, B_46), u1_struct_0(A_40)) | v1_tex_2(B_46, A_40) | ~m1_pre_topc(B_46, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.15/4.57  tff(c_1954, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1791, c_50])).
% 11.15/4.57  tff(c_1964, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_2', '#skF_2')) | v1_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1690, c_1954])).
% 11.15/4.57  tff(c_1965, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_2', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1964])).
% 11.15/4.57  tff(c_1339, plain, (![A_128, B_129]: (m1_subset_1('#skF_1'(A_128, B_129), k1_zfmisc_1(u1_struct_0(A_128))) | v1_tex_2(B_129, A_128) | ~m1_pre_topc(B_129, A_128) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.15/4.57  tff(c_56, plain, (![B_51, A_50]: (v1_subset_1(B_51, A_50) | B_51=A_50 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.15/4.57  tff(c_2507, plain, (![A_180, B_181]: (v1_subset_1('#skF_1'(A_180, B_181), u1_struct_0(A_180)) | u1_struct_0(A_180)='#skF_1'(A_180, B_181) | v1_tex_2(B_181, A_180) | ~m1_pre_topc(B_181, A_180) | ~l1_pre_topc(A_180))), inference(resolution, [status(thm)], [c_1339, c_56])).
% 11.15/4.57  tff(c_2513, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_3') | v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1791, c_2507])).
% 11.15/4.57  tff(c_2525, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_2', '#skF_2')) | '#skF_1'('#skF_2', '#skF_2')='#skF_1'('#skF_3', '#skF_3') | v1_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1791, c_1690, c_1690, c_2513])).
% 11.15/4.57  tff(c_2526, plain, ('#skF_1'('#skF_2', '#skF_2')='#skF_1'('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_1965, c_2525])).
% 11.15/4.57  tff(c_92, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_24, c_87])).
% 11.15/4.57  tff(c_96, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_92])).
% 11.15/4.57  tff(c_1691, plain, (k2_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_96])).
% 11.15/4.57  tff(c_236, plain, (![B_76, A_77]: (r1_tarski(u1_struct_0(B_76), u1_struct_0(A_77)) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.15/4.57  tff(c_250, plain, (![B_76]: (r1_tarski(u1_struct_0(B_76), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_76, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_236])).
% 11.15/4.57  tff(c_292, plain, (![B_80]: (r1_tarski(u1_struct_0(B_80), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_80, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_250])).
% 11.15/4.57  tff(c_297, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_292])).
% 11.15/4.57  tff(c_303, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_297])).
% 11.15/4.57  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.15/4.57  tff(c_307, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_303, c_2])).
% 11.15/4.57  tff(c_311, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_307])).
% 11.15/4.57  tff(c_1047, plain, (~r1_tarski(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_311])).
% 11.15/4.57  tff(c_1896, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_2'), '#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1691, c_1047])).
% 11.15/4.57  tff(c_2188, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_2'), '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1791, c_1896])).
% 11.15/4.57  tff(c_2544, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2526, c_2188])).
% 11.15/4.57  tff(c_2555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2544])).
% 11.15/4.57  tff(c_2556, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_307])).
% 11.15/4.57  tff(c_60, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.15/4.57  tff(c_97, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60])).
% 11.15/4.57  tff(c_136, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_97])).
% 11.15/4.57  tff(c_2563, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))!=g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_136])).
% 11.15/4.57  tff(c_16445, plain, (g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))!=g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_16429, c_2563])).
% 11.15/4.57  tff(c_17576, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))!=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_17455, c_16445])).
% 11.15/4.57  tff(c_21648, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))!=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21631, c_17576])).
% 11.15/4.57  tff(c_21653, plain, (v1_pre_topc(k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_21631, c_17583])).
% 11.15/4.57  tff(c_2564, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_96])).
% 11.15/4.57  tff(c_16451, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_2564])).
% 11.15/4.57  tff(c_17589, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16451])).
% 11.15/4.57  tff(c_38, plain, (![A_30, B_32]: (m1_pre_topc(A_30, g1_pre_topc(u1_struct_0(B_32), u1_pre_topc(B_32))) | ~m1_pre_topc(A_30, B_32) | ~l1_pre_topc(B_32) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.15/4.57  tff(c_17644, plain, (![A_30]: (m1_pre_topc(A_30, g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_30, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_30))), inference(superposition, [status(thm), theory('equality')], [c_17589, c_38])).
% 11.15/4.57  tff(c_17683, plain, (![A_30]: (m1_pre_topc(A_30, g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_30, '#skF_2') | ~l1_pre_topc(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_17644])).
% 11.15/4.57  tff(c_17590, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16429])).
% 11.15/4.57  tff(c_146, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_96, c_137])).
% 11.15/4.57  tff(c_151, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_146])).
% 11.15/4.57  tff(c_174, plain, (l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_151, c_160])).
% 11.15/4.57  tff(c_2560, plain, (l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_174])).
% 11.15/4.57  tff(c_8007, plain, (![B_354, A_355]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_354), u1_pre_topc(B_354)), A_355) | ~m1_pre_topc(B_354, A_355) | ~l1_pre_topc(A_355))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.15/4.57  tff(c_16269, plain, (![A_555]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_555) | ~m1_pre_topc('#skF_3', A_555) | ~l1_pre_topc(A_555))), inference(superposition, [status(thm), theory('equality')], [c_123, c_8007])).
% 11.15/4.57  tff(c_16163, plain, (![B_546]: (m1_pre_topc(B_546, '#skF_2') | ~m1_pre_topc(B_546, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2564, c_16149])).
% 11.15/4.57  tff(c_16179, plain, (![B_546]: (m1_pre_topc(B_546, '#skF_2') | ~m1_pre_topc(B_546, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16163])).
% 11.15/4.57  tff(c_16273, plain, (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~m1_pre_topc('#skF_3', g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_16269, c_16179])).
% 11.15/4.57  tff(c_16291, plain, (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~m1_pre_topc('#skF_3', g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_16273])).
% 11.15/4.57  tff(c_21203, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~m1_pre_topc('#skF_3', g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17590, c_17590, c_16291])).
% 11.15/4.57  tff(c_21204, plain, (~m1_pre_topc('#skF_3', g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_21203])).
% 11.15/4.57  tff(c_21207, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_17683, c_21204])).
% 11.15/4.57  tff(c_21211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_62, c_21207])).
% 11.15/4.57  tff(c_21212, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_21203])).
% 11.15/4.57  tff(c_21638, plain, (m1_pre_topc(k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21631, c_21212])).
% 11.15/4.57  tff(c_21642, plain, (k2_struct_0(k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21631, c_19429])).
% 11.15/4.57  tff(c_17103, plain, (![A_583, C_584]: (k1_pre_topc(A_583, k2_struct_0(C_584))=C_584 | ~m1_pre_topc(C_584, A_583) | ~v1_pre_topc(C_584) | ~m1_subset_1(k2_struct_0(C_584), k1_zfmisc_1(u1_struct_0(A_583))) | ~l1_pre_topc(A_583))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.15/4.57  tff(c_17115, plain, (![C_584]: (k1_pre_topc('#skF_2', k2_struct_0(C_584))=C_584 | ~m1_pre_topc(C_584, '#skF_2') | ~v1_pre_topc(C_584) | ~m1_subset_1(k2_struct_0(C_584), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16451, c_17103])).
% 11.15/4.57  tff(c_17131, plain, (![C_584]: (k1_pre_topc('#skF_2', k2_struct_0(C_584))=C_584 | ~m1_pre_topc(C_584, '#skF_2') | ~v1_pre_topc(C_584) | ~m1_subset_1(k2_struct_0(C_584), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_17115])).
% 11.15/4.57  tff(c_22676, plain, (![C_718]: (k1_pre_topc('#skF_2', k2_struct_0(C_718))=C_718 | ~m1_pre_topc(C_718, '#skF_2') | ~v1_pre_topc(C_718) | ~m1_subset_1(k2_struct_0(C_718), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_17131])).
% 11.15/4.57  tff(c_22679, plain, (k1_pre_topc('#skF_2', k2_struct_0(k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))))=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3')) | ~m1_pre_topc(k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3')), '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_21642, c_22676])).
% 11.15/4.57  tff(c_22696, plain, (k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_21653, c_21638, c_21642, c_22679])).
% 11.15/4.57  tff(c_197, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_151, c_183])).
% 11.15/4.57  tff(c_2561, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_197])).
% 11.15/4.57  tff(c_16448, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_2561])).
% 11.15/4.57  tff(c_17581, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16448])).
% 11.15/4.57  tff(c_16449, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_2560])).
% 11.15/4.57  tff(c_17579, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16449])).
% 11.15/4.57  tff(c_17792, plain, (![A_601]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_601), u1_pre_topc(A_601)), A_601) | ~l1_pre_topc(A_601) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_601), u1_pre_topc(A_601))))), inference(resolution, [status(thm)], [c_44, c_16149])).
% 11.15/4.57  tff(c_17806, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_17589, c_17792])).
% 11.15/4.57  tff(c_17821, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17579, c_17589, c_66, c_17806])).
% 11.15/4.57  tff(c_209, plain, (u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k2_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_174, c_91])).
% 11.15/4.57  tff(c_16352, plain, (u1_struct_0(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))=k2_struct_0(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_2556, c_209])).
% 11.15/4.57  tff(c_16431, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')))=k2_struct_0(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_16429, c_16352])).
% 11.15/4.57  tff(c_19152, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))=k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_17455, c_16431])).
% 11.15/4.57  tff(c_2562, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_151])).
% 11.15/4.57  tff(c_16447, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_2562])).
% 11.15/4.57  tff(c_17575, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_17455, c_16447])).
% 11.15/4.57  tff(c_19410, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))='#skF_1'('#skF_3', '#skF_3') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_17575, c_19407])).
% 11.15/4.57  tff(c_19426, plain, (k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17579, c_17581, c_19152, c_19410])).
% 11.15/4.57  tff(c_22682, plain, (k1_pre_topc('#skF_2', k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))))=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')) | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_2') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_19426, c_22676])).
% 11.15/4.57  tff(c_22698, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))=k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_17581, c_17821, c_19426, c_22682])).
% 11.15/4.57  tff(c_22871, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22696, c_22698])).
% 11.15/4.57  tff(c_22872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21648, c_22871])).
% 11.15/4.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.15/4.57  
% 11.15/4.57  Inference rules
% 11.15/4.57  ----------------------
% 11.15/4.57  #Ref     : 24
% 11.15/4.57  #Sup     : 4716
% 11.15/4.57  #Fact    : 0
% 11.15/4.57  #Define  : 0
% 11.15/4.57  #Split   : 21
% 11.15/4.57  #Chain   : 0
% 11.15/4.57  #Close   : 0
% 11.15/4.57  
% 11.15/4.57  Ordering : KBO
% 11.15/4.57  
% 11.15/4.57  Simplification rules
% 11.15/4.57  ----------------------
% 11.15/4.57  #Subsume      : 599
% 11.15/4.57  #Demod        : 14722
% 11.15/4.57  #Tautology    : 1655
% 11.15/4.57  #SimpNegUnit  : 72
% 11.15/4.57  #BackRed      : 404
% 11.15/4.57  
% 11.15/4.57  #Partial instantiations: 0
% 11.15/4.57  #Strategies tried      : 1
% 11.15/4.57  
% 11.15/4.57  Timing (in seconds)
% 11.15/4.57  ----------------------
% 11.15/4.58  Preprocessing        : 0.36
% 11.15/4.58  Parsing              : 0.20
% 11.15/4.58  CNF conversion       : 0.02
% 11.15/4.58  Main loop            : 3.38
% 11.15/4.58  Inferencing          : 0.75
% 11.15/4.58  Reduction            : 1.72
% 11.15/4.58  Demodulation         : 1.40
% 11.15/4.58  BG Simplification    : 0.10
% 11.15/4.58  Subsumption          : 0.59
% 11.15/4.58  Abstraction          : 0.15
% 11.15/4.58  MUC search           : 0.00
% 11.15/4.58  Cooper               : 0.00
% 11.15/4.58  Total                : 3.81
% 11.15/4.58  Index Insertion      : 0.00
% 11.15/4.58  Index Deletion       : 0.00
% 11.15/4.58  Index Matching       : 0.00
% 11.15/4.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
