%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 128 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 363 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
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

tff(f_92,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_1,A_45] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_45,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_54,plain,(
    ! [A_45] : ~ r2_hidden(A_45,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_56,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),B_51)
      | v2_tex_2(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v3_tdlat_3(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_1'(A_50,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v3_tdlat_3(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_62,plain,(
    ! [A_50] :
      ( v2_tex_2(k1_xboole_0,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v3_tdlat_3(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_59])).

tff(c_90,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1('#skF_3'(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [B_40] :
      ( ~ v3_tex_2(B_40,'#skF_4')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_109,plain,(
    ! [B_68] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_68),'#skF_4')
      | ~ v2_tex_2(B_68,'#skF_4')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_30])).

tff(c_119,plain,(
    ! [B_68] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_68),'#skF_4')
      | ~ v2_tex_2(B_68,'#skF_4')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_109])).

tff(c_121,plain,(
    ! [B_69] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_69),'#skF_4')
      | ~ v2_tex_2(B_69,'#skF_4')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_119])).

tff(c_134,plain,
    ( ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4')
    | ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_136,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_139,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_136])).

tff(c_142,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_139])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_142])).

tff(c_146,plain,(
    v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_64,plain,(
    ! [A_53,B_54] :
      ( v3_tex_2('#skF_3'(A_53,B_54),A_53)
      | ~ v2_tex_2(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v3_tdlat_3(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68,plain,(
    ! [A_53] :
      ( v3_tex_2('#skF_3'(A_53,k1_xboole_0),A_53)
      | ~ v2_tex_2(k1_xboole_0,A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v3_tdlat_3(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_64])).

tff(c_145,plain,(
    ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_150,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_145])).

tff(c_153,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_146,c_150])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_153])).

tff(c_156,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.27  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.15/1.27  
% 2.15/1.27  %Foreground sorts:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Background operators:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Foreground operators:
% 2.15/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.15/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.15/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.27  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.15/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.15/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.27  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.15/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.15/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.27  
% 2.15/1.28  tff(f_107, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.15/1.28  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.15/1.28  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.15/1.28  tff(f_69, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tex_2)).
% 2.15/1.28  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.15/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.28  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.15/1.28  tff(c_36, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.15/1.28  tff(c_34, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.15/1.28  tff(c_32, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.15/1.28  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.15/1.28  tff(c_46, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.28  tff(c_49, plain, (![A_1, A_45]: (~v1_xboole_0(A_1) | ~r2_hidden(A_45, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_46])).
% 2.15/1.28  tff(c_54, plain, (![A_45]: (~r2_hidden(A_45, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_49])).
% 2.15/1.28  tff(c_56, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), B_51) | v2_tex_2(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v3_tdlat_3(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.15/1.28  tff(c_59, plain, (![A_50]: (r2_hidden('#skF_1'(A_50, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_50) | ~l1_pre_topc(A_50) | ~v3_tdlat_3(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.15/1.28  tff(c_62, plain, (![A_50]: (v2_tex_2(k1_xboole_0, A_50) | ~l1_pre_topc(A_50) | ~v3_tdlat_3(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(negUnitSimplification, [status(thm)], [c_54, c_59])).
% 2.15/1.28  tff(c_90, plain, (![A_67, B_68]: (m1_subset_1('#skF_3'(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | ~v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v3_tdlat_3(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.15/1.28  tff(c_30, plain, (![B_40]: (~v3_tex_2(B_40, '#skF_4') | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.15/1.28  tff(c_109, plain, (![B_68]: (~v3_tex_2('#skF_3'('#skF_4', B_68), '#skF_4') | ~v2_tex_2(B_68, '#skF_4') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_30])).
% 2.15/1.28  tff(c_119, plain, (![B_68]: (~v3_tex_2('#skF_3'('#skF_4', B_68), '#skF_4') | ~v2_tex_2(B_68, '#skF_4') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_109])).
% 2.15/1.28  tff(c_121, plain, (![B_69]: (~v3_tex_2('#skF_3'('#skF_4', B_69), '#skF_4') | ~v2_tex_2(B_69, '#skF_4') | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_119])).
% 2.15/1.28  tff(c_134, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4') | ~v2_tex_2(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_4, c_121])).
% 2.15/1.28  tff(c_136, plain, (~v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_134])).
% 2.15/1.28  tff(c_139, plain, (~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_136])).
% 2.15/1.28  tff(c_142, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_139])).
% 2.15/1.28  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_142])).
% 2.15/1.28  tff(c_146, plain, (v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_134])).
% 2.15/1.28  tff(c_64, plain, (![A_53, B_54]: (v3_tex_2('#skF_3'(A_53, B_54), A_53) | ~v2_tex_2(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v3_tdlat_3(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.15/1.28  tff(c_68, plain, (![A_53]: (v3_tex_2('#skF_3'(A_53, k1_xboole_0), A_53) | ~v2_tex_2(k1_xboole_0, A_53) | ~l1_pre_topc(A_53) | ~v3_tdlat_3(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_4, c_64])).
% 2.15/1.28  tff(c_145, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4')), inference(splitRight, [status(thm)], [c_134])).
% 2.15/1.28  tff(c_150, plain, (~v2_tex_2(k1_xboole_0, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_145])).
% 2.15/1.28  tff(c_153, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_146, c_150])).
% 2.15/1.28  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_153])).
% 2.15/1.28  tff(c_156, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_49])).
% 2.15/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.15/1.28  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_2])).
% 2.15/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  Inference rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Ref     : 0
% 2.15/1.28  #Sup     : 20
% 2.15/1.28  #Fact    : 0
% 2.15/1.28  #Define  : 0
% 2.15/1.28  #Split   : 2
% 2.15/1.28  #Chain   : 0
% 2.15/1.28  #Close   : 0
% 2.15/1.28  
% 2.15/1.28  Ordering : KBO
% 2.15/1.28  
% 2.15/1.28  Simplification rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Subsume      : 4
% 2.15/1.28  #Demod        : 13
% 2.15/1.28  #Tautology    : 0
% 2.15/1.28  #SimpNegUnit  : 7
% 2.15/1.28  #BackRed      : 1
% 2.15/1.28  
% 2.15/1.28  #Partial instantiations: 0
% 2.15/1.28  #Strategies tried      : 1
% 2.15/1.28  
% 2.15/1.28  Timing (in seconds)
% 2.15/1.28  ----------------------
% 2.15/1.28  Preprocessing        : 0.31
% 2.15/1.28  Parsing              : 0.16
% 2.15/1.28  CNF conversion       : 0.02
% 2.15/1.28  Main loop            : 0.17
% 2.15/1.28  Inferencing          : 0.07
% 2.15/1.28  Reduction            : 0.05
% 2.15/1.28  Demodulation         : 0.03
% 2.15/1.28  BG Simplification    : 0.01
% 2.15/1.28  Subsumption          : 0.03
% 2.15/1.28  Abstraction          : 0.01
% 2.15/1.28  MUC search           : 0.00
% 2.15/1.28  Cooper               : 0.00
% 2.15/1.28  Total                : 0.51
% 2.15/1.28  Index Insertion      : 0.00
% 2.15/1.28  Index Deletion       : 0.00
% 2.15/1.28  Index Matching       : 0.00
% 2.15/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
