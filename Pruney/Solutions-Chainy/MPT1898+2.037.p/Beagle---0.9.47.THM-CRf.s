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
% DateTime   : Thu Dec  3 10:30:35 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 125 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 366 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_38,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_80,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_61)
      | v2_tex_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v3_tdlat_3(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,(
    ! [A_62] :
      ( r2_hidden('#skF_1'(A_62,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v3_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [A_62] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_62,k1_xboole_0))
      | v2_tex_2(k1_xboole_0,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v3_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_89,c_10])).

tff(c_103,plain,(
    ! [A_62] :
      ( v2_tex_2(k1_xboole_0,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v3_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_96])).

tff(c_202,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1('#skF_3'(A_91,B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ v2_tex_2(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v3_tdlat_3(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ! [B_41] :
      ( ~ v3_tex_2(B_41,'#skF_4')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_219,plain,(
    ! [B_92] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_92),'#skF_4')
      | ~ v2_tex_2(B_92,'#skF_4')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_202,c_32])).

tff(c_231,plain,(
    ! [B_92] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_92),'#skF_4')
      | ~ v2_tex_2(B_92,'#skF_4')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_219])).

tff(c_235,plain,(
    ! [B_95] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_95),'#skF_4')
      | ~ v2_tex_2(B_95,'#skF_4')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_231])).

tff(c_253,plain,
    ( ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4')
    | ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_235])).

tff(c_254,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_257,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_254])).

tff(c_260,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_257])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_260])).

tff(c_264,plain,(
    v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [A_78,B_79] :
      ( v3_tex_2('#skF_3'(A_78,B_79),A_78)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v3_tdlat_3(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_179,plain,(
    ! [A_78,A_2] :
      ( v3_tex_2('#skF_3'(A_78,A_2),A_78)
      | ~ v2_tex_2(A_2,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v3_tdlat_3(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ r1_tarski(A_2,u1_struct_0(A_78)) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_263,plain,(
    ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_275,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_179,c_263])).

tff(c_281,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_38,c_36,c_34,c_264,c_275])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:21:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.26  
% 2.38/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.27  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.38/1.27  
% 2.38/1.27  %Foreground sorts:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Background operators:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Foreground operators:
% 2.38/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.38/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.38/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.38/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.27  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.38/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.38/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.27  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.38/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.38/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.27  
% 2.38/1.28  tff(f_108, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.38/1.28  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.38/1.28  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.38/1.28  tff(f_70, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tex_2)).
% 2.38/1.28  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.38/1.28  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.38/1.28  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.38/1.28  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.28  tff(c_43, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.28  tff(c_47, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_43])).
% 2.38/1.28  tff(c_38, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.38/1.28  tff(c_36, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.38/1.28  tff(c_34, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.38/1.28  tff(c_80, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), B_61) | v2_tex_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v3_tdlat_3(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.38/1.28  tff(c_89, plain, (![A_62]: (r2_hidden('#skF_1'(A_62, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_62) | ~l1_pre_topc(A_62) | ~v3_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_2, c_80])).
% 2.38/1.28  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.38/1.28  tff(c_96, plain, (![A_62]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_62, k1_xboole_0)) | v2_tex_2(k1_xboole_0, A_62) | ~l1_pre_topc(A_62) | ~v3_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_89, c_10])).
% 2.38/1.28  tff(c_103, plain, (![A_62]: (v2_tex_2(k1_xboole_0, A_62) | ~l1_pre_topc(A_62) | ~v3_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_96])).
% 2.38/1.28  tff(c_202, plain, (![A_91, B_92]: (m1_subset_1('#skF_3'(A_91, B_92), k1_zfmisc_1(u1_struct_0(A_91))) | ~v2_tex_2(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v3_tdlat_3(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.38/1.28  tff(c_32, plain, (![B_41]: (~v3_tex_2(B_41, '#skF_4') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.38/1.28  tff(c_219, plain, (![B_92]: (~v3_tex_2('#skF_3'('#skF_4', B_92), '#skF_4') | ~v2_tex_2(B_92, '#skF_4') | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_202, c_32])).
% 2.38/1.28  tff(c_231, plain, (![B_92]: (~v3_tex_2('#skF_3'('#skF_4', B_92), '#skF_4') | ~v2_tex_2(B_92, '#skF_4') | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_219])).
% 2.38/1.28  tff(c_235, plain, (![B_95]: (~v3_tex_2('#skF_3'('#skF_4', B_95), '#skF_4') | ~v2_tex_2(B_95, '#skF_4') | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_231])).
% 2.38/1.28  tff(c_253, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4') | ~v2_tex_2(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_2, c_235])).
% 2.38/1.28  tff(c_254, plain, (~v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_253])).
% 2.38/1.28  tff(c_257, plain, (~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_103, c_254])).
% 2.38/1.28  tff(c_260, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_257])).
% 2.38/1.28  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_260])).
% 2.38/1.28  tff(c_264, plain, (v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_253])).
% 2.38/1.28  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.28  tff(c_172, plain, (![A_78, B_79]: (v3_tex_2('#skF_3'(A_78, B_79), A_78) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v3_tdlat_3(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.38/1.28  tff(c_179, plain, (![A_78, A_2]: (v3_tex_2('#skF_3'(A_78, A_2), A_78) | ~v2_tex_2(A_2, A_78) | ~l1_pre_topc(A_78) | ~v3_tdlat_3(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~r1_tarski(A_2, u1_struct_0(A_78)))), inference(resolution, [status(thm)], [c_6, c_172])).
% 2.38/1.28  tff(c_263, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4')), inference(splitRight, [status(thm)], [c_253])).
% 2.38/1.28  tff(c_275, plain, (~v2_tex_2(k1_xboole_0, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_179, c_263])).
% 2.38/1.28  tff(c_281, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_38, c_36, c_34, c_264, c_275])).
% 2.38/1.28  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_281])).
% 2.38/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.28  
% 2.38/1.28  Inference rules
% 2.38/1.28  ----------------------
% 2.38/1.28  #Ref     : 0
% 2.38/1.28  #Sup     : 45
% 2.38/1.28  #Fact    : 0
% 2.38/1.28  #Define  : 0
% 2.38/1.28  #Split   : 1
% 2.38/1.28  #Chain   : 0
% 2.38/1.28  #Close   : 0
% 2.38/1.28  
% 2.38/1.28  Ordering : KBO
% 2.38/1.28  
% 2.38/1.28  Simplification rules
% 2.38/1.28  ----------------------
% 2.38/1.28  #Subsume      : 11
% 2.38/1.28  #Demod        : 25
% 2.38/1.28  #Tautology    : 3
% 2.38/1.28  #SimpNegUnit  : 5
% 2.38/1.28  #BackRed      : 0
% 2.38/1.28  
% 2.38/1.28  #Partial instantiations: 0
% 2.38/1.28  #Strategies tried      : 1
% 2.38/1.28  
% 2.38/1.28  Timing (in seconds)
% 2.38/1.28  ----------------------
% 2.38/1.28  Preprocessing        : 0.31
% 2.38/1.28  Parsing              : 0.17
% 2.38/1.28  CNF conversion       : 0.02
% 2.38/1.28  Main loop            : 0.21
% 2.38/1.28  Inferencing          : 0.09
% 2.38/1.28  Reduction            : 0.06
% 2.38/1.28  Demodulation         : 0.04
% 2.38/1.28  BG Simplification    : 0.01
% 2.38/1.28  Subsumption          : 0.05
% 2.38/1.28  Abstraction          : 0.01
% 2.38/1.28  MUC search           : 0.00
% 2.38/1.28  Cooper               : 0.00
% 2.38/1.28  Total                : 0.56
% 2.38/1.28  Index Insertion      : 0.00
% 2.38/1.28  Index Deletion       : 0.00
% 2.38/1.28  Index Matching       : 0.00
% 2.38/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
