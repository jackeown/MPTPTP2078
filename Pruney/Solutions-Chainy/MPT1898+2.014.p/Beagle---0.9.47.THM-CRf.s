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
% DateTime   : Thu Dec  3 10:30:32 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 119 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 350 expanded)
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

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),B_53)
      | v2_tex_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v3_tdlat_3(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_69,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_2'(A_54,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v3_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v3_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_78,plain,(
    ! [A_54] :
      ( v2_tex_2(k1_xboole_0,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v3_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_105,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1('#skF_4'(A_70,B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ v2_tex_2(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v3_tdlat_3(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [B_41] :
      ( ~ v3_tex_2(B_41,'#skF_5')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_122,plain,(
    ! [B_71] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_71),'#skF_5')
      | ~ v2_tex_2(B_71,'#skF_5')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_105,c_32])).

tff(c_131,plain,(
    ! [B_71] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_71),'#skF_5')
      | ~ v2_tex_2(B_71,'#skF_5')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_122])).

tff(c_134,plain,(
    ! [B_74] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_74),'#skF_5')
      | ~ v2_tex_2(B_74,'#skF_5')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_131])).

tff(c_147,plain,
    ( ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5')
    | ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_148,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_151,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_148])).

tff(c_154,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_151])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_154])).

tff(c_158,plain,(
    v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_86,plain,(
    ! [A_59,B_60] :
      ( v3_tex_2('#skF_4'(A_59,B_60),A_59)
      | ~ v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v3_tdlat_3(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_90,plain,(
    ! [A_59] :
      ( v3_tex_2('#skF_4'(A_59,k1_xboole_0),A_59)
      | ~ v2_tex_2(k1_xboole_0,A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v3_tdlat_3(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_157,plain,(
    ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_162,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_157])).

tff(c_165,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_158,c_162])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.26  
% 2.25/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.26  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.25/1.26  
% 2.25/1.26  %Foreground sorts:
% 2.25/1.26  
% 2.25/1.26  
% 2.25/1.26  %Background operators:
% 2.25/1.26  
% 2.25/1.26  
% 2.25/1.26  %Foreground operators:
% 2.25/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.25/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.25/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.26  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.25/1.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.25/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.26  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.25/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.25/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.25/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.25/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.26  
% 2.25/1.28  tff(f_106, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.25/1.28  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.25/1.28  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.25/1.28  tff(f_68, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 2.25/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.25/1.28  tff(f_91, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.25/1.28  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.25/1.28  tff(c_38, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.25/1.28  tff(c_36, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.25/1.28  tff(c_34, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.25/1.28  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.25/1.28  tff(c_8, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.25/1.28  tff(c_64, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), B_53) | v2_tex_2(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v3_tdlat_3(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.25/1.28  tff(c_69, plain, (![A_54]: (r2_hidden('#skF_2'(A_54, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_54) | ~l1_pre_topc(A_54) | ~v3_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_8, c_64])).
% 2.25/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.28  tff(c_74, plain, (![A_54]: (~v1_xboole_0(k1_xboole_0) | v2_tex_2(k1_xboole_0, A_54) | ~l1_pre_topc(A_54) | ~v3_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_69, c_2])).
% 2.25/1.28  tff(c_78, plain, (![A_54]: (v2_tex_2(k1_xboole_0, A_54) | ~l1_pre_topc(A_54) | ~v3_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_74])).
% 2.25/1.28  tff(c_105, plain, (![A_70, B_71]: (m1_subset_1('#skF_4'(A_70, B_71), k1_zfmisc_1(u1_struct_0(A_70))) | ~v2_tex_2(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v3_tdlat_3(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.25/1.28  tff(c_32, plain, (![B_41]: (~v3_tex_2(B_41, '#skF_5') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.25/1.28  tff(c_122, plain, (![B_71]: (~v3_tex_2('#skF_4'('#skF_5', B_71), '#skF_5') | ~v2_tex_2(B_71, '#skF_5') | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_105, c_32])).
% 2.25/1.28  tff(c_131, plain, (![B_71]: (~v3_tex_2('#skF_4'('#skF_5', B_71), '#skF_5') | ~v2_tex_2(B_71, '#skF_5') | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_122])).
% 2.25/1.28  tff(c_134, plain, (![B_74]: (~v3_tex_2('#skF_4'('#skF_5', B_74), '#skF_5') | ~v2_tex_2(B_74, '#skF_5') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_131])).
% 2.25/1.28  tff(c_147, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5') | ~v2_tex_2(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_8, c_134])).
% 2.25/1.28  tff(c_148, plain, (~v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_147])).
% 2.25/1.28  tff(c_151, plain, (~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_78, c_148])).
% 2.25/1.28  tff(c_154, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_151])).
% 2.25/1.28  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_154])).
% 2.25/1.28  tff(c_158, plain, (v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_147])).
% 2.25/1.28  tff(c_86, plain, (![A_59, B_60]: (v3_tex_2('#skF_4'(A_59, B_60), A_59) | ~v2_tex_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v3_tdlat_3(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.25/1.28  tff(c_90, plain, (![A_59]: (v3_tex_2('#skF_4'(A_59, k1_xboole_0), A_59) | ~v2_tex_2(k1_xboole_0, A_59) | ~l1_pre_topc(A_59) | ~v3_tdlat_3(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_8, c_86])).
% 2.25/1.28  tff(c_157, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5')), inference(splitRight, [status(thm)], [c_147])).
% 2.25/1.28  tff(c_162, plain, (~v2_tex_2(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_157])).
% 2.25/1.28  tff(c_165, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_158, c_162])).
% 2.25/1.28  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_165])).
% 2.25/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.28  
% 2.25/1.28  Inference rules
% 2.25/1.28  ----------------------
% 2.25/1.28  #Ref     : 0
% 2.25/1.28  #Sup     : 22
% 2.25/1.28  #Fact    : 0
% 2.25/1.28  #Define  : 0
% 2.25/1.28  #Split   : 1
% 2.25/1.28  #Chain   : 0
% 2.25/1.28  #Close   : 0
% 2.25/1.28  
% 2.25/1.28  Ordering : KBO
% 2.25/1.28  
% 2.25/1.28  Simplification rules
% 2.25/1.28  ----------------------
% 2.25/1.28  #Subsume      : 4
% 2.25/1.28  #Demod        : 15
% 2.25/1.28  #Tautology    : 2
% 2.25/1.28  #SimpNegUnit  : 4
% 2.25/1.28  #BackRed      : 0
% 2.25/1.28  
% 2.25/1.28  #Partial instantiations: 0
% 2.25/1.28  #Strategies tried      : 1
% 2.25/1.28  
% 2.25/1.28  Timing (in seconds)
% 2.25/1.28  ----------------------
% 2.25/1.28  Preprocessing        : 0.31
% 2.25/1.28  Parsing              : 0.16
% 2.25/1.28  CNF conversion       : 0.02
% 2.25/1.28  Main loop            : 0.18
% 2.25/1.28  Inferencing          : 0.07
% 2.25/1.28  Reduction            : 0.05
% 2.25/1.28  Demodulation         : 0.03
% 2.25/1.28  BG Simplification    : 0.01
% 2.25/1.28  Subsumption          : 0.03
% 2.25/1.28  Abstraction          : 0.01
% 2.25/1.28  MUC search           : 0.00
% 2.25/1.28  Cooper               : 0.00
% 2.25/1.28  Total                : 0.52
% 2.25/1.28  Index Insertion      : 0.00
% 2.25/1.28  Index Deletion       : 0.00
% 2.25/1.28  Index Matching       : 0.00
% 2.25/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
