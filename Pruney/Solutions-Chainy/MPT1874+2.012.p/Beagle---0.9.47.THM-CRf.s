%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:38 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 158 expanded)
%              Number of leaves         :   30 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 458 expanded)
%              Number of equality atoms :   10 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_78,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_57,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_63,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_60])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tarski(A_7),k1_zfmisc_1(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_59,B_60,C_61] :
      ( k9_subset_1(u1_struct_0(A_59),B_60,k2_pre_topc(A_59,C_61)) = C_61
      | ~ r1_tarski(C_61,B_60)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_223,plain,(
    ! [A_69,B_70,A_71] :
      ( k9_subset_1(u1_struct_0(A_69),B_70,k2_pre_topc(A_69,k1_tarski(A_71))) = k1_tarski(A_71)
      | ~ r1_tarski(k1_tarski(A_71),B_70)
      | ~ v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69)
      | ~ r2_hidden(A_71,u1_struct_0(A_69)) ) ),
    inference(resolution,[status(thm)],[c_10,c_147])).

tff(c_74,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_88,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_83])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_89,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_26])).

tff(c_229,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_89])).

tff(c_236,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_229])).

tff(c_237,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_236])).

tff(c_239,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_242,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_239])).

tff(c_245,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_242])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_245])).

tff(c_248,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_248])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.40  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.47/1.40  
% 2.47/1.40  %Foreground sorts:
% 2.47/1.40  
% 2.47/1.40  
% 2.47/1.40  %Background operators:
% 2.47/1.40  
% 2.47/1.40  
% 2.47/1.40  %Foreground operators:
% 2.47/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.47/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.47/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.47/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.47/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.47/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.47/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.40  
% 2.47/1.41  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.47/1.41  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.47/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.47/1.41  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.47/1.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.47/1.41  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.47/1.41  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.47/1.41  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.47/1.41  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.41  tff(c_41, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.41  tff(c_45, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.47/1.41  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_57, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.41  tff(c_60, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_57])).
% 2.47/1.41  tff(c_63, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_45, c_60])).
% 2.47/1.41  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_14, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.47/1.41  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k1_tarski(A_7), k1_zfmisc_1(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.41  tff(c_147, plain, (![A_59, B_60, C_61]: (k9_subset_1(u1_struct_0(A_59), B_60, k2_pre_topc(A_59, C_61))=C_61 | ~r1_tarski(C_61, B_60) | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(A_59))) | ~v2_tex_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.41  tff(c_223, plain, (![A_69, B_70, A_71]: (k9_subset_1(u1_struct_0(A_69), B_70, k2_pre_topc(A_69, k1_tarski(A_71)))=k1_tarski(A_71) | ~r1_tarski(k1_tarski(A_71), B_70) | ~v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69) | ~r2_hidden(A_71, u1_struct_0(A_69)))), inference(resolution, [status(thm)], [c_10, c_147])).
% 2.47/1.41  tff(c_74, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.41  tff(c_83, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.47/1.41  tff(c_88, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_63, c_83])).
% 2.47/1.41  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.41  tff(c_89, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_26])).
% 2.47/1.41  tff(c_229, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_89])).
% 2.47/1.41  tff(c_236, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_229])).
% 2.47/1.41  tff(c_237, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_236])).
% 2.47/1.41  tff(c_239, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_237])).
% 2.47/1.41  tff(c_242, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_239])).
% 2.47/1.41  tff(c_245, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_242])).
% 2.47/1.41  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_245])).
% 2.47/1.41  tff(c_248, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_237])).
% 2.47/1.41  tff(c_252, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_248])).
% 2.47/1.41  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_252])).
% 2.47/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.41  
% 2.47/1.41  Inference rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Ref     : 0
% 2.47/1.41  #Sup     : 41
% 2.47/1.41  #Fact    : 0
% 2.47/1.41  #Define  : 0
% 2.47/1.41  #Split   : 3
% 2.47/1.41  #Chain   : 0
% 2.47/1.41  #Close   : 0
% 2.47/1.41  
% 2.47/1.41  Ordering : KBO
% 2.47/1.41  
% 2.47/1.41  Simplification rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Subsume      : 5
% 2.47/1.41  #Demod        : 22
% 2.47/1.41  #Tautology    : 16
% 2.47/1.41  #SimpNegUnit  : 9
% 2.47/1.41  #BackRed      : 1
% 2.47/1.41  
% 2.47/1.41  #Partial instantiations: 0
% 2.47/1.41  #Strategies tried      : 1
% 2.47/1.41  
% 2.47/1.41  Timing (in seconds)
% 2.47/1.41  ----------------------
% 2.47/1.41  Preprocessing        : 0.35
% 2.47/1.41  Parsing              : 0.18
% 2.47/1.41  CNF conversion       : 0.03
% 2.47/1.41  Main loop            : 0.23
% 2.47/1.41  Inferencing          : 0.09
% 2.47/1.41  Reduction            : 0.06
% 2.47/1.41  Demodulation         : 0.04
% 2.47/1.41  BG Simplification    : 0.02
% 2.47/1.41  Subsumption          : 0.04
% 2.47/1.41  Abstraction          : 0.01
% 2.47/1.41  MUC search           : 0.00
% 2.47/1.41  Cooper               : 0.00
% 2.47/1.41  Total                : 0.61
% 2.47/1.41  Index Insertion      : 0.00
% 2.47/1.41  Index Deletion       : 0.00
% 2.47/1.41  Index Matching       : 0.00
% 2.47/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
