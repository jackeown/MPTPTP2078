%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:46 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 144 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 422 expanded)
%              Number of equality atoms :   10 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k1_tarski(A_32),k1_zfmisc_1(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_48,c_6])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_81,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k1_tarski(A_1),k1_zfmisc_1(B_2))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_196,plain,(
    ! [A_73,B_74,C_75] :
      ( k9_subset_1(u1_struct_0(A_73),B_74,k2_pre_topc(A_73,C_75)) = C_75
      | ~ r1_tarski(C_75,B_74)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_344,plain,(
    ! [A_102,B_103,A_104] :
      ( k9_subset_1(u1_struct_0(A_102),B_103,k2_pre_topc(A_102,k1_tarski(A_104))) = k1_tarski(A_104)
      | ~ r1_tarski(k1_tarski(A_104),B_103)
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102)
      | ~ r2_hidden(A_104,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_2,c_196])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_99,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_80])).

tff(c_22,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_100,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_22])).

tff(c_350,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_100])).

tff(c_357,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_350])).

tff(c_358,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_357])).

tff(c_360,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_363,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_360])).

tff(c_366,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_363])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_366])).

tff(c_369,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_373,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_369])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_373])).

tff(c_378,plain,(
    ! [A_38] : ~ r2_hidden(A_38,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:31:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.46  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.11/1.46  
% 3.11/1.46  %Foreground sorts:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Background operators:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Foreground operators:
% 3.11/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.11/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.46  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.11/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.11/1.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.11/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.46  
% 3.11/1.48  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 3.11/1.48  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.11/1.48  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.11/1.48  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.11/1.48  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.11/1.48  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 3.11/1.48  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.11/1.48  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_48, plain, (![A_32, B_33]: (m1_subset_1(k1_tarski(A_32), k1_zfmisc_1(B_33)) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.11/1.48  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.11/1.48  tff(c_52, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_48, c_6])).
% 3.11/1.48  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_54, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.11/1.48  tff(c_63, plain, (![A_38]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_54])).
% 3.11/1.48  tff(c_81, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_63])).
% 3.11/1.48  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.48  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k1_tarski(A_1), k1_zfmisc_1(B_2)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.11/1.48  tff(c_196, plain, (![A_73, B_74, C_75]: (k9_subset_1(u1_struct_0(A_73), B_74, k2_pre_topc(A_73, C_75))=C_75 | ~r1_tarski(C_75, B_74) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_73))) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.48  tff(c_344, plain, (![A_102, B_103, A_104]: (k9_subset_1(u1_struct_0(A_102), B_103, k2_pre_topc(A_102, k1_tarski(A_104)))=k1_tarski(A_104) | ~r1_tarski(k1_tarski(A_104), B_103) | ~v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102) | ~r2_hidden(A_104, u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_2, c_196])).
% 3.11/1.48  tff(c_64, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.11/1.48  tff(c_80, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_64])).
% 3.11/1.48  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_81, c_80])).
% 3.11/1.48  tff(c_22, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.48  tff(c_100, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_22])).
% 3.11/1.48  tff(c_350, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_344, c_100])).
% 3.11/1.48  tff(c_357, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_350])).
% 3.11/1.48  tff(c_358, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_357])).
% 3.11/1.48  tff(c_360, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_358])).
% 3.11/1.48  tff(c_363, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_360])).
% 3.11/1.48  tff(c_366, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_363])).
% 3.11/1.48  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_366])).
% 3.11/1.48  tff(c_369, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_358])).
% 3.11/1.48  tff(c_373, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_369])).
% 3.11/1.48  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_373])).
% 3.11/1.48  tff(c_378, plain, (![A_38]: (~r2_hidden(A_38, '#skF_3'))), inference(splitRight, [status(thm)], [c_63])).
% 3.11/1.48  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_378, c_24])).
% 3.11/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.48  
% 3.11/1.48  Inference rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Ref     : 0
% 3.11/1.48  #Sup     : 73
% 3.11/1.48  #Fact    : 0
% 3.11/1.48  #Define  : 0
% 3.11/1.48  #Split   : 6
% 3.11/1.48  #Chain   : 0
% 3.11/1.48  #Close   : 0
% 3.11/1.48  
% 3.11/1.48  Ordering : KBO
% 3.11/1.48  
% 3.11/1.48  Simplification rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Subsume      : 5
% 3.11/1.48  #Demod        : 22
% 3.11/1.48  #Tautology    : 27
% 3.11/1.48  #SimpNegUnit  : 9
% 3.11/1.48  #BackRed      : 2
% 3.11/1.48  
% 3.11/1.48  #Partial instantiations: 0
% 3.11/1.48  #Strategies tried      : 1
% 3.11/1.48  
% 3.11/1.48  Timing (in seconds)
% 3.11/1.48  ----------------------
% 3.11/1.48  Preprocessing        : 0.34
% 3.11/1.48  Parsing              : 0.18
% 3.11/1.48  CNF conversion       : 0.02
% 3.11/1.48  Main loop            : 0.33
% 3.11/1.48  Inferencing          : 0.13
% 3.11/1.48  Reduction            : 0.09
% 3.11/1.48  Demodulation         : 0.05
% 3.11/1.48  BG Simplification    : 0.02
% 3.11/1.48  Subsumption          : 0.07
% 3.11/1.48  Abstraction          : 0.02
% 3.11/1.48  MUC search           : 0.00
% 3.11/1.48  Cooper               : 0.00
% 3.11/1.48  Total                : 0.70
% 3.11/1.48  Index Insertion      : 0.00
% 3.11/1.49  Index Deletion       : 0.00
% 3.11/1.49  Index Matching       : 0.00
% 3.11/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
