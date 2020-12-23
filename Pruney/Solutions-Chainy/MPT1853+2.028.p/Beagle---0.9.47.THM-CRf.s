%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:03 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 199 expanded)
%              Number of leaves         :   32 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  217 ( 551 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc13_tex_2)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_107,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ v1_xboole_0(B)
           => ( ~ v1_xboole_0(B)
              & ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_237,plain,(
    ! [A_72,B_73] :
      ( m1_pre_topc(k1_tex_2(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_239,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_237])).

tff(c_242,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_239])).

tff(c_243,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_242])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_246,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_243,c_4])).

tff(c_249,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_246])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_42,B_43] :
      ( ~ v2_struct_0(k1_tex_2(A_42,B_43))
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_62,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_65,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62])).

tff(c_66,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_65])).

tff(c_254,plain,(
    ! [A_82,B_83] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_82),B_83),u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_struct_0(A_82)
      | v7_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_85,plain,(
    ! [A_48,B_49] :
      ( m1_pre_topc(k1_tex_2(A_48,B_49),A_48)
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_87,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_85])).

tff(c_90,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_87])).

tff(c_91,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_90])).

tff(c_68,plain,(
    ! [A_44,B_45] :
      ( v7_struct_0(k1_tex_2(A_44,B_45))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_71,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_68])).

tff(c_74,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71])).

tff(c_75,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_74])).

tff(c_181,plain,(
    ! [B_62,A_63] :
      ( ~ v7_struct_0(B_62)
      | v1_tex_2(B_62,A_63)
      | v2_struct_0(B_62)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63)
      | v7_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_67,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_184,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_181,c_67])).

tff(c_187,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91,c_75,c_184])).

tff(c_188,plain,(
    v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_66,c_187])).

tff(c_54,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_54])).

tff(c_189,plain,(
    ! [A_64,B_65] :
      ( ~ v7_struct_0(A_64)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_64),B_65),u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_struct_0(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_198,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_189])).

tff(c_207,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_188,c_198])).

tff(c_208,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_207])).

tff(c_211,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_211])).

tff(c_216,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_260,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_254,c_216])).

tff(c_264,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_260])).

tff(c_265,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_264])).

tff(c_266,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_269,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_266])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_269])).

tff(c_274,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_275,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_217,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( m1_subset_1(u1_struct_0(B_8),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_285,plain,(
    ! [B_86,A_87] :
      ( v1_subset_1(u1_struct_0(B_86),u1_struct_0(A_87))
      | ~ m1_subset_1(u1_struct_0(B_86),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v1_tex_2(B_86,A_87)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_289,plain,(
    ! [B_8,A_6] :
      ( v1_subset_1(u1_struct_0(B_8),u1_struct_0(A_6))
      | ~ v1_tex_2(B_8,A_6)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_285])).

tff(c_276,plain,(
    ! [B_84,A_85] :
      ( ~ v1_subset_1(B_84,u1_struct_0(A_85))
      | v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_struct_0(A_85)
      | ~ v7_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_291,plain,(
    ! [B_90,A_91] :
      ( ~ v1_subset_1(u1_struct_0(B_90),u1_struct_0(A_91))
      | v1_xboole_0(u1_struct_0(B_90))
      | ~ l1_struct_0(A_91)
      | ~ v7_struct_0(A_91)
      | v2_struct_0(A_91)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_8,c_276])).

tff(c_296,plain,(
    ! [B_92,A_93] :
      ( v1_xboole_0(u1_struct_0(B_92))
      | ~ l1_struct_0(A_93)
      | ~ v7_struct_0(A_93)
      | v2_struct_0(A_93)
      | ~ v1_tex_2(B_92,A_93)
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_289,c_291])).

tff(c_302,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_217,c_296])).

tff(c_307,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_243,c_274,c_275,c_302])).

tff(c_308,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_307])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_311,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_308,c_6])).

tff(c_314,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_311])).

tff(c_317,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_314])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  
% 2.35/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.30  
% 2.35/1.30  %Foreground sorts:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Background operators:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Foreground operators:
% 2.35/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.35/1.30  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.35/1.30  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.35/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.35/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.35/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.30  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.35/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.30  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.35/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.35/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.30  
% 2.35/1.32  tff(f_174, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.35/1.32  tff(f_121, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.35/1.32  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.35/1.32  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.35/1.32  tff(f_135, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.35/1.32  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 2.35/1.32  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.35/1.32  tff(f_148, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.35/1.32  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.35/1.32  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.35/1.32  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~v1_xboole_0(B) => (~v1_xboole_0(B) & ~v1_subset_1(B, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tex_2)).
% 2.35/1.32  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.35/1.32  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.35/1.32  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.35/1.32  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.35/1.32  tff(c_237, plain, (![A_72, B_73]: (m1_pre_topc(k1_tex_2(A_72, B_73), A_72) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.35/1.32  tff(c_239, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_237])).
% 2.35/1.32  tff(c_242, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_239])).
% 2.35/1.32  tff(c_243, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_242])).
% 2.35/1.32  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.35/1.32  tff(c_246, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_243, c_4])).
% 2.35/1.32  tff(c_249, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_246])).
% 2.35/1.32  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.32  tff(c_59, plain, (![A_42, B_43]: (~v2_struct_0(k1_tex_2(A_42, B_43)) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l1_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.35/1.32  tff(c_62, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_59])).
% 2.35/1.32  tff(c_65, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62])).
% 2.35/1.32  tff(c_66, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_65])).
% 2.35/1.32  tff(c_254, plain, (![A_82, B_83]: (v1_subset_1(k6_domain_1(u1_struct_0(A_82), B_83), u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_struct_0(A_82) | v7_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.35/1.32  tff(c_85, plain, (![A_48, B_49]: (m1_pre_topc(k1_tex_2(A_48, B_49), A_48) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.35/1.32  tff(c_87, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_85])).
% 2.35/1.32  tff(c_90, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_87])).
% 2.35/1.32  tff(c_91, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_90])).
% 2.35/1.32  tff(c_68, plain, (![A_44, B_45]: (v7_struct_0(k1_tex_2(A_44, B_45)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.35/1.32  tff(c_71, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_68])).
% 2.35/1.32  tff(c_74, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_71])).
% 2.35/1.32  tff(c_75, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_74])).
% 2.35/1.32  tff(c_181, plain, (![B_62, A_63]: (~v7_struct_0(B_62) | v1_tex_2(B_62, A_63) | v2_struct_0(B_62) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63) | v7_struct_0(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.32  tff(c_48, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.35/1.32  tff(c_67, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 2.35/1.32  tff(c_184, plain, (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_181, c_67])).
% 2.35/1.32  tff(c_187, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_91, c_75, c_184])).
% 2.35/1.32  tff(c_188, plain, (v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_66, c_187])).
% 2.35/1.32  tff(c_54, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.35/1.32  tff(c_76, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_67, c_54])).
% 2.35/1.32  tff(c_189, plain, (![A_64, B_65]: (~v7_struct_0(A_64) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_64), B_65), u1_struct_0(A_64)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_struct_0(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.35/1.32  tff(c_198, plain, (~v7_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_189])).
% 2.35/1.32  tff(c_207, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_188, c_198])).
% 2.35/1.32  tff(c_208, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_207])).
% 2.35/1.32  tff(c_211, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_208])).
% 2.35/1.32  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_211])).
% 2.35/1.32  tff(c_216, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 2.35/1.32  tff(c_260, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_254, c_216])).
% 2.35/1.32  tff(c_264, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_260])).
% 2.35/1.32  tff(c_265, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_264])).
% 2.35/1.32  tff(c_266, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_265])).
% 2.35/1.32  tff(c_269, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_266])).
% 2.35/1.32  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_269])).
% 2.35/1.32  tff(c_274, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_265])).
% 2.35/1.32  tff(c_275, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_265])).
% 2.35/1.32  tff(c_217, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 2.35/1.32  tff(c_8, plain, (![B_8, A_6]: (m1_subset_1(u1_struct_0(B_8), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.35/1.32  tff(c_285, plain, (![B_86, A_87]: (v1_subset_1(u1_struct_0(B_86), u1_struct_0(A_87)) | ~m1_subset_1(u1_struct_0(B_86), k1_zfmisc_1(u1_struct_0(A_87))) | ~v1_tex_2(B_86, A_87) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.35/1.32  tff(c_289, plain, (![B_8, A_6]: (v1_subset_1(u1_struct_0(B_8), u1_struct_0(A_6)) | ~v1_tex_2(B_8, A_6) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_285])).
% 2.35/1.32  tff(c_276, plain, (![B_84, A_85]: (~v1_subset_1(B_84, u1_struct_0(A_85)) | v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_struct_0(A_85) | ~v7_struct_0(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.35/1.32  tff(c_291, plain, (![B_90, A_91]: (~v1_subset_1(u1_struct_0(B_90), u1_struct_0(A_91)) | v1_xboole_0(u1_struct_0(B_90)) | ~l1_struct_0(A_91) | ~v7_struct_0(A_91) | v2_struct_0(A_91) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_8, c_276])).
% 2.35/1.32  tff(c_296, plain, (![B_92, A_93]: (v1_xboole_0(u1_struct_0(B_92)) | ~l1_struct_0(A_93) | ~v7_struct_0(A_93) | v2_struct_0(A_93) | ~v1_tex_2(B_92, A_93) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_289, c_291])).
% 2.35/1.32  tff(c_302, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_217, c_296])).
% 2.35/1.32  tff(c_307, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_243, c_274, c_275, c_302])).
% 2.35/1.32  tff(c_308, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_307])).
% 2.35/1.32  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.32  tff(c_311, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_308, c_6])).
% 2.35/1.32  tff(c_314, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_311])).
% 2.35/1.32  tff(c_317, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_314])).
% 2.35/1.32  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_317])).
% 2.35/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  Inference rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Ref     : 0
% 2.35/1.32  #Sup     : 41
% 2.35/1.32  #Fact    : 0
% 2.35/1.32  #Define  : 0
% 2.35/1.32  #Split   : 3
% 2.35/1.32  #Chain   : 0
% 2.35/1.32  #Close   : 0
% 2.35/1.32  
% 2.35/1.32  Ordering : KBO
% 2.35/1.32  
% 2.35/1.32  Simplification rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Subsume      : 4
% 2.35/1.32  #Demod        : 42
% 2.35/1.32  #Tautology    : 9
% 2.35/1.32  #SimpNegUnit  : 21
% 2.35/1.32  #BackRed      : 0
% 2.35/1.32  
% 2.35/1.32  #Partial instantiations: 0
% 2.35/1.32  #Strategies tried      : 1
% 2.35/1.32  
% 2.35/1.32  Timing (in seconds)
% 2.35/1.32  ----------------------
% 2.35/1.32  Preprocessing        : 0.34
% 2.35/1.32  Parsing              : 0.18
% 2.35/1.32  CNF conversion       : 0.02
% 2.35/1.32  Main loop            : 0.22
% 2.35/1.32  Inferencing          : 0.09
% 2.35/1.32  Reduction            : 0.07
% 2.35/1.32  Demodulation         : 0.05
% 2.35/1.32  BG Simplification    : 0.02
% 2.35/1.32  Subsumption          : 0.04
% 2.35/1.32  Abstraction          : 0.01
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.60
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
