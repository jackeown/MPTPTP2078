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
% DateTime   : Thu Dec  3 10:29:02 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 171 expanded)
%              Number of leaves         :   26 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 ( 466 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_62,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_221,plain,(
    ! [A_59,B_60] :
      ( ~ v2_struct_0(k1_tex_2(A_59,B_60))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_224,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_227,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_224])).

tff(c_228,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_227])).

tff(c_229,plain,(
    ! [A_61,B_62] :
      ( m1_pre_topc(k1_tex_2(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_231,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_229])).

tff(c_234,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_231])).

tff(c_235,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_234])).

tff(c_36,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_69,plain,(
    ! [A_38,B_39] :
      ( m1_pre_topc(k1_tex_2(A_38,B_39),A_38)
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_71,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_74,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_71])).

tff(c_75,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_74])).

tff(c_53,plain,(
    ! [A_34,B_35] :
      ( ~ v2_struct_0(k1_tex_2(A_34,B_35))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_59,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56])).

tff(c_60,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_59])).

tff(c_44,plain,(
    ! [A_32,B_33] :
      ( v1_pre_topc(k1_tex_2(A_32,B_33))
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_47,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_50,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_47])).

tff(c_51,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_50])).

tff(c_62,plain,(
    ! [B_36,A_37] :
      ( u1_struct_0(B_36) = '#skF_1'(A_37,B_36)
      | v1_tex_2(B_36,A_37)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_65,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_52])).

tff(c_68,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_65])).

tff(c_83,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_68])).

tff(c_177,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(u1_struct_0(A_57),B_58) = u1_struct_0(k1_tex_2(A_57,B_58))
      | ~ m1_pre_topc(k1_tex_2(A_57,B_58),A_57)
      | ~ v1_pre_topc(k1_tex_2(A_57,B_58))
      | v2_struct_0(k1_tex_2(A_57,B_58))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_179,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_177])).

tff(c_182,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_51,c_83,c_179])).

tff(c_183,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_60,c_182])).

tff(c_42,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_61,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42])).

tff(c_184,plain,(
    v1_subset_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_61])).

tff(c_10,plain,(
    ! [A_5,B_11] :
      ( ~ v1_subset_1('#skF_1'(A_5,B_11),u1_struct_0(A_5))
      | v1_tex_2(B_11,A_5)
      | ~ m1_pre_topc(B_11,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_208,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_184,c_10])).

tff(c_211,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_211])).

tff(c_215,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_238,plain,(
    ! [B_67,A_68] :
      ( ~ v1_tex_2(B_67,A_68)
      | v2_struct_0(B_67)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v7_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_244,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_215,c_238])).

tff(c_248,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_235,c_244])).

tff(c_249,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_228,c_248])).

tff(c_260,plain,(
    ! [A_75,B_76] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_75),B_76),u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_struct_0(A_75)
      | v7_struct_0(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_214,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_216,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_216])).

tff(c_219,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_266,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_260,c_219])).

tff(c_270,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_266])).

tff(c_271,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_249,c_270])).

tff(c_274,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_271])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.35  
% 2.40/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.35  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.35  
% 2.40/1.35  %Foreground sorts:
% 2.40/1.35  
% 2.40/1.35  
% 2.40/1.35  %Background operators:
% 2.40/1.35  
% 2.40/1.35  
% 2.40/1.35  %Foreground operators:
% 2.40/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.35  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.40/1.35  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.40/1.35  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.40/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.40/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.35  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.40/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.35  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.40/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.35  
% 2.40/1.37  tff(f_135, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.40/1.37  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.40/1.37  tff(f_96, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.40/1.37  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.40/1.37  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.40/1.37  tff(f_48, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.40/1.37  tff(f_122, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 2.40/1.37  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.40/1.37  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.37  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.40/1.37  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.40/1.37  tff(c_221, plain, (![A_59, B_60]: (~v2_struct_0(k1_tex_2(A_59, B_60)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.40/1.37  tff(c_224, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_221])).
% 2.40/1.37  tff(c_227, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_224])).
% 2.40/1.37  tff(c_228, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_227])).
% 2.40/1.37  tff(c_229, plain, (![A_61, B_62]: (m1_pre_topc(k1_tex_2(A_61, B_62), A_61) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.40/1.37  tff(c_231, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_229])).
% 2.40/1.37  tff(c_234, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_231])).
% 2.40/1.37  tff(c_235, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_234])).
% 2.40/1.37  tff(c_36, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.40/1.37  tff(c_52, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 2.40/1.37  tff(c_69, plain, (![A_38, B_39]: (m1_pre_topc(k1_tex_2(A_38, B_39), A_38) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.40/1.37  tff(c_71, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_69])).
% 2.40/1.37  tff(c_74, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_71])).
% 2.40/1.37  tff(c_75, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_74])).
% 2.40/1.37  tff(c_53, plain, (![A_34, B_35]: (~v2_struct_0(k1_tex_2(A_34, B_35)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.40/1.37  tff(c_56, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_53])).
% 2.40/1.37  tff(c_59, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56])).
% 2.40/1.37  tff(c_60, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_59])).
% 2.40/1.37  tff(c_44, plain, (![A_32, B_33]: (v1_pre_topc(k1_tex_2(A_32, B_33)) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.40/1.37  tff(c_47, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.40/1.37  tff(c_50, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_47])).
% 2.40/1.37  tff(c_51, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_50])).
% 2.40/1.37  tff(c_62, plain, (![B_36, A_37]: (u1_struct_0(B_36)='#skF_1'(A_37, B_36) | v1_tex_2(B_36, A_37) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.40/1.37  tff(c_65, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_52])).
% 2.40/1.37  tff(c_68, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_65])).
% 2.40/1.37  tff(c_83, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_68])).
% 2.40/1.37  tff(c_177, plain, (![A_57, B_58]: (k6_domain_1(u1_struct_0(A_57), B_58)=u1_struct_0(k1_tex_2(A_57, B_58)) | ~m1_pre_topc(k1_tex_2(A_57, B_58), A_57) | ~v1_pre_topc(k1_tex_2(A_57, B_58)) | v2_struct_0(k1_tex_2(A_57, B_58)) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.40/1.37  tff(c_179, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_75, c_177])).
% 2.40/1.37  tff(c_182, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_51, c_83, c_179])).
% 2.40/1.37  tff(c_183, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_60, c_182])).
% 2.40/1.37  tff(c_42, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.40/1.37  tff(c_61, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42])).
% 2.40/1.37  tff(c_184, plain, (v1_subset_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_61])).
% 2.40/1.37  tff(c_10, plain, (![A_5, B_11]: (~v1_subset_1('#skF_1'(A_5, B_11), u1_struct_0(A_5)) | v1_tex_2(B_11, A_5) | ~m1_pre_topc(B_11, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.40/1.37  tff(c_208, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_184, c_10])).
% 2.40/1.37  tff(c_211, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75, c_208])).
% 2.40/1.37  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_211])).
% 2.40/1.37  tff(c_215, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.40/1.37  tff(c_238, plain, (![B_67, A_68]: (~v1_tex_2(B_67, A_68) | v2_struct_0(B_67) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68) | ~v7_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.37  tff(c_244, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_215, c_238])).
% 2.40/1.37  tff(c_248, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_235, c_244])).
% 2.40/1.37  tff(c_249, plain, (~v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_228, c_248])).
% 2.40/1.37  tff(c_260, plain, (![A_75, B_76]: (v1_subset_1(k6_domain_1(u1_struct_0(A_75), B_76), u1_struct_0(A_75)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_struct_0(A_75) | v7_struct_0(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.40/1.37  tff(c_214, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 2.40/1.37  tff(c_216, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.40/1.37  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_216])).
% 2.40/1.37  tff(c_219, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.40/1.37  tff(c_266, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_260, c_219])).
% 2.40/1.37  tff(c_270, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_266])).
% 2.40/1.37  tff(c_271, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_249, c_270])).
% 2.40/1.37  tff(c_274, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_271])).
% 2.40/1.37  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_274])).
% 2.40/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.37  
% 2.40/1.37  Inference rules
% 2.40/1.37  ----------------------
% 2.40/1.37  #Ref     : 0
% 2.40/1.37  #Sup     : 39
% 2.40/1.37  #Fact    : 0
% 2.40/1.37  #Define  : 0
% 2.40/1.37  #Split   : 5
% 2.40/1.37  #Chain   : 0
% 2.40/1.37  #Close   : 0
% 2.40/1.37  
% 2.40/1.37  Ordering : KBO
% 2.40/1.37  
% 2.40/1.37  Simplification rules
% 2.40/1.37  ----------------------
% 2.40/1.37  #Subsume      : 10
% 2.40/1.37  #Demod        : 41
% 2.40/1.37  #Tautology    : 11
% 2.40/1.37  #SimpNegUnit  : 25
% 2.40/1.37  #BackRed      : 1
% 2.40/1.37  
% 2.40/1.37  #Partial instantiations: 0
% 2.40/1.37  #Strategies tried      : 1
% 2.40/1.37  
% 2.40/1.37  Timing (in seconds)
% 2.40/1.37  ----------------------
% 2.40/1.37  Preprocessing        : 0.33
% 2.40/1.37  Parsing              : 0.18
% 2.40/1.37  CNF conversion       : 0.02
% 2.40/1.37  Main loop            : 0.21
% 2.40/1.37  Inferencing          : 0.07
% 2.40/1.37  Reduction            : 0.07
% 2.40/1.37  Demodulation         : 0.05
% 2.40/1.37  BG Simplification    : 0.02
% 2.40/1.37  Subsumption          : 0.03
% 2.40/1.37  Abstraction          : 0.01
% 2.40/1.37  MUC search           : 0.00
% 2.40/1.37  Cooper               : 0.00
% 2.40/1.37  Total                : 0.57
% 2.40/1.37  Index Insertion      : 0.00
% 2.40/1.37  Index Deletion       : 0.00
% 2.40/1.37  Index Matching       : 0.00
% 2.40/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
