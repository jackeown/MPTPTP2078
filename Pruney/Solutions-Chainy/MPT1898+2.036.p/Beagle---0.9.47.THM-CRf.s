%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:35 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 117 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 350 expanded)
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_55)
      | v2_tex_2(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v3_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_1'(A_56,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_69,plain,(
    ! [A_56] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_56,k1_xboole_0))
      | v2_tex_2(k1_xboole_0,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_64,c_8])).

tff(c_73,plain,(
    ! [A_56] :
      ( v2_tex_2(k1_xboole_0,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_94,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1('#skF_3'(A_68,B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ v2_tex_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v3_tdlat_3(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [B_40] :
      ( ~ v3_tex_2(B_40,'#skF_4')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_111,plain,(
    ! [B_69] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_69),'#skF_4')
      | ~ v2_tex_2(B_69,'#skF_4')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_94,c_30])).

tff(c_120,plain,(
    ! [B_69] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_69),'#skF_4')
      | ~ v2_tex_2(B_69,'#skF_4')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_111])).

tff(c_122,plain,(
    ! [B_70] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_70),'#skF_4')
      | ~ v2_tex_2(B_70,'#skF_4')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_120])).

tff(c_135,plain,
    ( ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4')
    | ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_122])).

tff(c_136,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_140,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_136])).

tff(c_143,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_140])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_143])).

tff(c_147,plain,(
    v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_53,plain,(
    ! [A_51,B_52] :
      ( v3_tex_2('#skF_3'(A_51,B_52),A_51)
      | ~ v2_tex_2(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v3_tdlat_3(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    ! [A_51] :
      ( v3_tex_2('#skF_3'(A_51,k1_xboole_0),A_51)
      | ~ v2_tex_2(k1_xboole_0,A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v3_tdlat_3(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_146,plain,(
    ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_150,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_146])).

tff(c_153,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_147,c_150])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.21  
% 2.08/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.22  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.08/1.22  
% 2.08/1.22  %Foreground sorts:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Background operators:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Foreground operators:
% 2.08/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.08/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.08/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.22  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.08/1.22  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.08/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.22  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.08/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.08/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.22  
% 2.20/1.23  tff(f_106, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.20/1.23  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.20/1.23  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.20/1.23  tff(f_68, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 2.20/1.23  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.20/1.23  tff(f_91, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.20/1.23  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.23  tff(c_36, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.23  tff(c_34, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.23  tff(c_32, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.23  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.23  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.23  tff(c_59, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), B_55) | v2_tex_2(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v3_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.23  tff(c_64, plain, (![A_56]: (r2_hidden('#skF_1'(A_56, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_56) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.20/1.23  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.23  tff(c_69, plain, (![A_56]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_56, k1_xboole_0)) | v2_tex_2(k1_xboole_0, A_56) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_64, c_8])).
% 2.20/1.23  tff(c_73, plain, (![A_56]: (v2_tex_2(k1_xboole_0, A_56) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_69])).
% 2.20/1.23  tff(c_94, plain, (![A_68, B_69]: (m1_subset_1('#skF_3'(A_68, B_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~v2_tex_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v3_tdlat_3(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.20/1.23  tff(c_30, plain, (![B_40]: (~v3_tex_2(B_40, '#skF_4') | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.23  tff(c_111, plain, (![B_69]: (~v3_tex_2('#skF_3'('#skF_4', B_69), '#skF_4') | ~v2_tex_2(B_69, '#skF_4') | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_94, c_30])).
% 2.20/1.23  tff(c_120, plain, (![B_69]: (~v3_tex_2('#skF_3'('#skF_4', B_69), '#skF_4') | ~v2_tex_2(B_69, '#skF_4') | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_111])).
% 2.20/1.23  tff(c_122, plain, (![B_70]: (~v3_tex_2('#skF_3'('#skF_4', B_70), '#skF_4') | ~v2_tex_2(B_70, '#skF_4') | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_120])).
% 2.20/1.23  tff(c_135, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4') | ~v2_tex_2(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_4, c_122])).
% 2.20/1.23  tff(c_136, plain, (~v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_135])).
% 2.20/1.23  tff(c_140, plain, (~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_73, c_136])).
% 2.20/1.23  tff(c_143, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_140])).
% 2.20/1.23  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_143])).
% 2.20/1.23  tff(c_147, plain, (v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 2.20/1.23  tff(c_53, plain, (![A_51, B_52]: (v3_tex_2('#skF_3'(A_51, B_52), A_51) | ~v2_tex_2(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v3_tdlat_3(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.20/1.23  tff(c_57, plain, (![A_51]: (v3_tex_2('#skF_3'(A_51, k1_xboole_0), A_51) | ~v2_tex_2(k1_xboole_0, A_51) | ~l1_pre_topc(A_51) | ~v3_tdlat_3(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_4, c_53])).
% 2.20/1.23  tff(c_146, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 2.20/1.23  tff(c_150, plain, (~v2_tex_2(k1_xboole_0, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_57, c_146])).
% 2.20/1.23  tff(c_153, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_147, c_150])).
% 2.20/1.23  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_153])).
% 2.20/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.23  
% 2.20/1.23  Inference rules
% 2.20/1.23  ----------------------
% 2.20/1.23  #Ref     : 0
% 2.20/1.23  #Sup     : 20
% 2.20/1.23  #Fact    : 0
% 2.20/1.23  #Define  : 0
% 2.20/1.23  #Split   : 1
% 2.20/1.23  #Chain   : 0
% 2.20/1.23  #Close   : 0
% 2.20/1.23  
% 2.20/1.23  Ordering : KBO
% 2.20/1.23  
% 2.20/1.23  Simplification rules
% 2.20/1.23  ----------------------
% 2.20/1.23  #Subsume      : 4
% 2.20/1.23  #Demod        : 15
% 2.20/1.23  #Tautology    : 1
% 2.20/1.23  #SimpNegUnit  : 4
% 2.20/1.23  #BackRed      : 0
% 2.20/1.23  
% 2.20/1.23  #Partial instantiations: 0
% 2.20/1.23  #Strategies tried      : 1
% 2.20/1.23  
% 2.20/1.23  Timing (in seconds)
% 2.20/1.23  ----------------------
% 2.20/1.23  Preprocessing        : 0.31
% 2.20/1.23  Parsing              : 0.16
% 2.20/1.23  CNF conversion       : 0.02
% 2.20/1.23  Main loop            : 0.16
% 2.20/1.23  Inferencing          : 0.07
% 2.20/1.23  Reduction            : 0.04
% 2.20/1.23  Demodulation         : 0.03
% 2.24/1.24  BG Simplification    : 0.01
% 2.24/1.24  Subsumption          : 0.03
% 2.24/1.24  Abstraction          : 0.01
% 2.24/1.24  MUC search           : 0.00
% 2.24/1.24  Cooper               : 0.00
% 2.24/1.24  Total                : 0.50
% 2.24/1.24  Index Insertion      : 0.00
% 2.24/1.24  Index Deletion       : 0.00
% 2.24/1.24  Index Matching       : 0.00
% 2.24/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
