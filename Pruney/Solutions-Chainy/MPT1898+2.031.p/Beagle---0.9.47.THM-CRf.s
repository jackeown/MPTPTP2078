%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 164 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  156 ( 582 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & ~ v2_struct_0(B)
          & v1_pre_topc(B)
          & v2_pre_topc(B)
          & v1_tdlat_3(B)
          & v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc11_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_96,axiom,(
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

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_tdlat_3('#skF_1'(A_4))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_4] :
      ( m1_pre_topc('#skF_1'(A_4),A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_subset_1(u1_struct_0(B_3),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [B_37,A_38] :
      ( v2_tex_2(u1_struct_0(B_37),A_38)
      | ~ v1_tdlat_3(B_37)
      | ~ m1_subset_1(u1_struct_0(B_37),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(B_37,A_38)
      | v2_struct_0(B_37)
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_65,plain,(
    ! [B_3,A_1] :
      ( v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v1_tdlat_3(B_3)
      | v2_struct_0(B_3)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_30,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_57,plain,(
    ! [A_35,B_36] :
      ( v3_tex_2('#skF_2'(A_35,B_36),A_35)
      | ~ v2_tex_2(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v3_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_108,plain,(
    ! [A_48,B_49] :
      ( v3_tex_2('#skF_2'(A_48,u1_struct_0(B_49)),A_48)
      | ~ v2_tex_2(u1_struct_0(B_49),A_48)
      | ~ v3_tdlat_3(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48)
      | ~ m1_pre_topc(B_49,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_75,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1('#skF_2'(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ v2_tex_2(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v3_tdlat_3(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [B_20] :
      ( ~ v3_tex_2(B_20,'#skF_3')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_83,plain,(
    ! [B_44] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_44),'#skF_3')
      | ~ v2_tex_2(B_44,'#skF_3')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_75,c_26])).

tff(c_88,plain,(
    ! [B_44] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_44),'#skF_3')
      | ~ v2_tex_2(B_44,'#skF_3')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_83])).

tff(c_90,plain,(
    ! [B_45] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_45),'#skF_3')
      | ~ v2_tex_2(B_45,'#skF_3')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_88])).

tff(c_98,plain,(
    ! [B_3] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_105,plain,(
    ! [B_3] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_112,plain,(
    ! [B_49] :
      ( ~ v2_tex_2(u1_struct_0(B_49),'#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_49,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_108,c_105])).

tff(c_115,plain,(
    ! [B_49] :
      ( ~ v2_tex_2(u1_struct_0(B_49),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_49,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_30,c_112])).

tff(c_117,plain,(
    ! [B_50] :
      ( ~ v2_tex_2(u1_struct_0(B_50),'#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_115])).

tff(c_121,plain,(
    ! [B_3] :
      ( ~ v1_tdlat_3(B_3)
      | v2_struct_0(B_3)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_65,c_117])).

tff(c_124,plain,(
    ! [B_3] :
      ( ~ v1_tdlat_3(B_3)
      | v2_struct_0(B_3)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_121])).

tff(c_127,plain,(
    ! [B_53] :
      ( ~ v1_tdlat_3(B_53)
      | v2_struct_0(B_53)
      | ~ m1_pre_topc(B_53,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_124])).

tff(c_131,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_134,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_131])).

tff(c_135,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_134])).

tff(c_136,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_139,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_142,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_139])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_142])).

tff(c_145,plain,(
    v2_struct_0('#skF_1'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_12,plain,(
    ! [A_4] :
      ( ~ v2_struct_0('#skF_1'(A_4))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_149,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_12])).

tff(c_152,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.26  
% 2.50/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.26  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2
% 2.50/1.26  
% 2.50/1.26  %Foreground sorts:
% 2.50/1.26  
% 2.50/1.26  
% 2.50/1.26  %Background operators:
% 2.50/1.26  
% 2.50/1.26  
% 2.50/1.26  %Foreground operators:
% 2.50/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.26  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.50/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.26  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.50/1.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.50/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.26  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.50/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.26  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.50/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.50/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.26  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.50/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.26  
% 2.50/1.28  tff(f_111, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.50/1.28  tff(f_53, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((((m1_pre_topc(B, A) & ~v2_struct_0(B)) & v1_pre_topc(B)) & v2_pre_topc(B)) & v1_tdlat_3(B)) & v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc11_tex_2)).
% 2.50/1.28  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 2.50/1.28  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 2.50/1.28  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.50/1.28  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.50/1.28  tff(c_32, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.50/1.28  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.50/1.28  tff(c_6, plain, (![A_4]: (v1_tdlat_3('#skF_1'(A_4)) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.28  tff(c_14, plain, (![A_4]: (m1_pre_topc('#skF_1'(A_4), A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.28  tff(c_2, plain, (![B_3, A_1]: (m1_subset_1(u1_struct_0(B_3), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.28  tff(c_61, plain, (![B_37, A_38]: (v2_tex_2(u1_struct_0(B_37), A_38) | ~v1_tdlat_3(B_37) | ~m1_subset_1(u1_struct_0(B_37), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(B_37, A_38) | v2_struct_0(B_37) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.50/1.28  tff(c_65, plain, (![B_3, A_1]: (v2_tex_2(u1_struct_0(B_3), A_1) | ~v1_tdlat_3(B_3) | v2_struct_0(B_3) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_61])).
% 2.50/1.28  tff(c_30, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.50/1.28  tff(c_57, plain, (![A_35, B_36]: (v3_tex_2('#skF_2'(A_35, B_36), A_35) | ~v2_tex_2(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v3_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.50/1.28  tff(c_108, plain, (![A_48, B_49]: (v3_tex_2('#skF_2'(A_48, u1_struct_0(B_49)), A_48) | ~v2_tex_2(u1_struct_0(B_49), A_48) | ~v3_tdlat_3(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48) | ~m1_pre_topc(B_49, A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.50/1.28  tff(c_75, plain, (![A_43, B_44]: (m1_subset_1('#skF_2'(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~v2_tex_2(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v3_tdlat_3(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.50/1.28  tff(c_26, plain, (![B_20]: (~v3_tex_2(B_20, '#skF_3') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.50/1.28  tff(c_83, plain, (![B_44]: (~v3_tex_2('#skF_2'('#skF_3', B_44), '#skF_3') | ~v2_tex_2(B_44, '#skF_3') | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_26])).
% 2.50/1.28  tff(c_88, plain, (![B_44]: (~v3_tex_2('#skF_2'('#skF_3', B_44), '#skF_3') | ~v2_tex_2(B_44, '#skF_3') | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_83])).
% 2.50/1.28  tff(c_90, plain, (![B_45]: (~v3_tex_2('#skF_2'('#skF_3', B_45), '#skF_3') | ~v2_tex_2(B_45, '#skF_3') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_88])).
% 2.50/1.28  tff(c_98, plain, (![B_3]: (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | ~m1_pre_topc(B_3, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_2, c_90])).
% 2.50/1.28  tff(c_105, plain, (![B_3]: (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_98])).
% 2.50/1.28  tff(c_112, plain, (![B_49]: (~v2_tex_2(u1_struct_0(B_49), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_49, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_108, c_105])).
% 2.50/1.28  tff(c_115, plain, (![B_49]: (~v2_tex_2(u1_struct_0(B_49), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_49, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_30, c_112])).
% 2.50/1.28  tff(c_117, plain, (![B_50]: (~v2_tex_2(u1_struct_0(B_50), '#skF_3') | ~m1_pre_topc(B_50, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_115])).
% 2.50/1.28  tff(c_121, plain, (![B_3]: (~v1_tdlat_3(B_3) | v2_struct_0(B_3) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_65, c_117])).
% 2.50/1.28  tff(c_124, plain, (![B_3]: (~v1_tdlat_3(B_3) | v2_struct_0(B_3) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_121])).
% 2.50/1.28  tff(c_127, plain, (![B_53]: (~v1_tdlat_3(B_53) | v2_struct_0(B_53) | ~m1_pre_topc(B_53, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_124])).
% 2.50/1.28  tff(c_131, plain, (~v1_tdlat_3('#skF_1'('#skF_3')) | v2_struct_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_127])).
% 2.50/1.28  tff(c_134, plain, (~v1_tdlat_3('#skF_1'('#skF_3')) | v2_struct_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_131])).
% 2.50/1.28  tff(c_135, plain, (~v1_tdlat_3('#skF_1'('#skF_3')) | v2_struct_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_134])).
% 2.50/1.28  tff(c_136, plain, (~v1_tdlat_3('#skF_1'('#skF_3'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.50/1.28  tff(c_139, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_136])).
% 2.50/1.28  tff(c_142, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_139])).
% 2.50/1.28  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_142])).
% 2.50/1.28  tff(c_145, plain, (v2_struct_0('#skF_1'('#skF_3'))), inference(splitRight, [status(thm)], [c_135])).
% 2.50/1.28  tff(c_12, plain, (![A_4]: (~v2_struct_0('#skF_1'(A_4)) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.28  tff(c_149, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_145, c_12])).
% 2.50/1.28  tff(c_152, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_149])).
% 2.50/1.28  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_152])).
% 2.50/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.28  
% 2.50/1.28  Inference rules
% 2.50/1.28  ----------------------
% 2.50/1.28  #Ref     : 0
% 2.50/1.28  #Sup     : 16
% 2.50/1.28  #Fact    : 0
% 2.50/1.28  #Define  : 0
% 2.50/1.28  #Split   : 1
% 2.50/1.28  #Chain   : 0
% 2.50/1.28  #Close   : 0
% 2.50/1.28  
% 2.50/1.28  Ordering : KBO
% 2.50/1.28  
% 2.50/1.28  Simplification rules
% 2.50/1.28  ----------------------
% 2.50/1.28  #Subsume      : 3
% 2.50/1.28  #Demod        : 18
% 2.50/1.28  #Tautology    : 1
% 2.50/1.28  #SimpNegUnit  : 7
% 2.50/1.28  #BackRed      : 0
% 2.50/1.28  
% 2.50/1.28  #Partial instantiations: 0
% 2.50/1.28  #Strategies tried      : 1
% 2.50/1.28  
% 2.50/1.28  Timing (in seconds)
% 2.50/1.28  ----------------------
% 2.50/1.28  Preprocessing        : 0.31
% 2.50/1.28  Parsing              : 0.17
% 2.50/1.28  CNF conversion       : 0.02
% 2.50/1.28  Main loop            : 0.20
% 2.50/1.28  Inferencing          : 0.09
% 2.50/1.28  Reduction            : 0.05
% 2.50/1.28  Demodulation         : 0.03
% 2.50/1.28  BG Simplification    : 0.01
% 2.50/1.28  Subsumption          : 0.04
% 2.50/1.28  Abstraction          : 0.01
% 2.50/1.28  MUC search           : 0.00
% 2.50/1.29  Cooper               : 0.00
% 2.50/1.29  Total                : 0.54
% 2.50/1.29  Index Insertion      : 0.00
% 2.50/1.29  Index Deletion       : 0.00
% 2.50/1.29  Index Matching       : 0.00
% 2.50/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
