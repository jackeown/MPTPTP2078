%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:30 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 145 expanded)
%              Number of leaves         :   31 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 397 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => ( C = D
                        | r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),D))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ v1_xboole_0(C_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(C_53))
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [A_1,A_55] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_55,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_75])).

tff(c_82,plain,(
    ! [A_55] : ~ r2_hidden(A_55,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_103,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_3'(A_68,B_69),B_69)
      | v2_tex_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v3_tdlat_3(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_108,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_3'(A_68,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v3_tdlat_3(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_112,plain,(
    ! [A_68] :
      ( v2_tex_2(k1_xboole_0,A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v3_tdlat_3(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_108])).

tff(c_167,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1('#skF_4'(A_89,B_90),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ v2_tex_2(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v3_tdlat_3(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    ! [B_45] :
      ( ~ v3_tex_2(B_45,'#skF_5')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_189,plain,(
    ! [B_90] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_90),'#skF_5')
      | ~ v2_tex_2(B_90,'#skF_5')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_167,c_34])).

tff(c_200,plain,(
    ! [B_90] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_90),'#skF_5')
      | ~ v2_tex_2(B_90,'#skF_5')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_189])).

tff(c_202,plain,(
    ! [B_91] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_91),'#skF_5')
      | ~ v2_tex_2(B_91,'#skF_5')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_200])).

tff(c_222,plain,
    ( ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5')
    | ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_202])).

tff(c_223,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_226,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_223])).

tff(c_229,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_226])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_229])).

tff(c_233,plain,(
    v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_93,plain,(
    ! [A_64,B_65] :
      ( v3_tex_2('#skF_4'(A_64,B_65),A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v3_tdlat_3(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_100,plain,(
    ! [A_64] :
      ( v3_tex_2('#skF_4'(A_64,k1_xboole_0),A_64)
      | ~ v2_tex_2(k1_xboole_0,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v3_tdlat_3(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_232,plain,(
    ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_236,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_232])).

tff(c_239,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_233,c_236])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_239])).

tff(c_242,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_59,plain,(
    ! [B_50,A_51] :
      ( v1_xboole_0(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_59])).

tff(c_68,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_10,plain,(
    ! [A_11] :
      ( v1_xboole_0('#skF_1'(A_11))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [A_11] : ~ l1_pre_topc(A_11) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_10])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_36])).

tff(c_74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.33  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.42/1.33  
% 2.42/1.33  %Foreground sorts:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Background operators:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Foreground operators:
% 2.42/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.42/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.42/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.42/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.42/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.33  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.42/1.33  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.42/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.42/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.33  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.42/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.42/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.42/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.42/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.33  
% 2.42/1.35  tff(f_120, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.42/1.35  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.42/1.35  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.42/1.35  tff(f_82, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 2.42/1.35  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.42/1.35  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.42/1.35  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 2.42/1.35  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.42/1.35  tff(c_40, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.42/1.35  tff(c_38, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.42/1.35  tff(c_36, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.42/1.35  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.35  tff(c_75, plain, (![C_53, B_54, A_55]: (~v1_xboole_0(C_53) | ~m1_subset_1(B_54, k1_zfmisc_1(C_53)) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.35  tff(c_81, plain, (![A_1, A_55]: (~v1_xboole_0(A_1) | ~r2_hidden(A_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_75])).
% 2.42/1.35  tff(c_82, plain, (![A_55]: (~r2_hidden(A_55, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_81])).
% 2.42/1.35  tff(c_103, plain, (![A_68, B_69]: (r2_hidden('#skF_3'(A_68, B_69), B_69) | v2_tex_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v3_tdlat_3(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.42/1.35  tff(c_108, plain, (![A_68]: (r2_hidden('#skF_3'(A_68, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_68) | ~l1_pre_topc(A_68) | ~v3_tdlat_3(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_2, c_103])).
% 2.42/1.35  tff(c_112, plain, (![A_68]: (v2_tex_2(k1_xboole_0, A_68) | ~l1_pre_topc(A_68) | ~v3_tdlat_3(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(negUnitSimplification, [status(thm)], [c_82, c_108])).
% 2.42/1.35  tff(c_167, plain, (![A_89, B_90]: (m1_subset_1('#skF_4'(A_89, B_90), k1_zfmisc_1(u1_struct_0(A_89))) | ~v2_tex_2(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v3_tdlat_3(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.42/1.35  tff(c_34, plain, (![B_45]: (~v3_tex_2(B_45, '#skF_5') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.42/1.35  tff(c_189, plain, (![B_90]: (~v3_tex_2('#skF_4'('#skF_5', B_90), '#skF_5') | ~v2_tex_2(B_90, '#skF_5') | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_167, c_34])).
% 2.42/1.35  tff(c_200, plain, (![B_90]: (~v3_tex_2('#skF_4'('#skF_5', B_90), '#skF_5') | ~v2_tex_2(B_90, '#skF_5') | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_189])).
% 2.42/1.35  tff(c_202, plain, (![B_91]: (~v3_tex_2('#skF_4'('#skF_5', B_91), '#skF_5') | ~v2_tex_2(B_91, '#skF_5') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_200])).
% 2.42/1.35  tff(c_222, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5') | ~v2_tex_2(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_2, c_202])).
% 2.42/1.35  tff(c_223, plain, (~v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_222])).
% 2.42/1.35  tff(c_226, plain, (~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_112, c_223])).
% 2.42/1.35  tff(c_229, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_226])).
% 2.42/1.35  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_229])).
% 2.42/1.35  tff(c_233, plain, (v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_222])).
% 2.42/1.35  tff(c_93, plain, (![A_64, B_65]: (v3_tex_2('#skF_4'(A_64, B_65), A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v3_tdlat_3(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.42/1.35  tff(c_100, plain, (![A_64]: (v3_tex_2('#skF_4'(A_64, k1_xboole_0), A_64) | ~v2_tex_2(k1_xboole_0, A_64) | ~l1_pre_topc(A_64) | ~v3_tdlat_3(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_2, c_93])).
% 2.42/1.35  tff(c_232, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5')), inference(splitRight, [status(thm)], [c_222])).
% 2.42/1.35  tff(c_236, plain, (~v2_tex_2(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_100, c_232])).
% 2.42/1.35  tff(c_239, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_233, c_236])).
% 2.42/1.35  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_239])).
% 2.42/1.35  tff(c_242, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_81])).
% 2.42/1.35  tff(c_59, plain, (![B_50, A_51]: (v1_xboole_0(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.42/1.35  tff(c_67, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2, c_59])).
% 2.42/1.35  tff(c_68, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitLeft, [status(thm)], [c_67])).
% 2.42/1.35  tff(c_10, plain, (![A_11]: (v1_xboole_0('#skF_1'(A_11)) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.35  tff(c_70, plain, (![A_11]: (~l1_pre_topc(A_11))), inference(negUnitSimplification, [status(thm)], [c_68, c_10])).
% 2.42/1.35  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_36])).
% 2.42/1.35  tff(c_74, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_67])).
% 2.42/1.35  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_74])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 38
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 3
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 9
% 2.42/1.35  #Demod        : 15
% 2.42/1.35  #Tautology    : 0
% 2.42/1.35  #SimpNegUnit  : 12
% 2.42/1.35  #BackRed      : 4
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.35  ----------------------
% 2.42/1.35  Preprocessing        : 0.33
% 2.42/1.35  Parsing              : 0.17
% 2.42/1.35  CNF conversion       : 0.03
% 2.42/1.35  Main loop            : 0.24
% 2.42/1.35  Inferencing          : 0.10
% 2.42/1.35  Reduction            : 0.06
% 2.42/1.35  Demodulation         : 0.04
% 2.42/1.35  BG Simplification    : 0.02
% 2.42/1.35  Subsumption          : 0.04
% 2.42/1.35  Abstraction          : 0.01
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.60
% 2.42/1.35  Index Insertion      : 0.00
% 2.42/1.35  Index Deletion       : 0.00
% 2.42/1.35  Index Matching       : 0.00
% 2.42/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
