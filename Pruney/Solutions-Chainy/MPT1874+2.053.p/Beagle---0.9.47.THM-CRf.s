%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:44 EST 2020

% Result     : Theorem 12.23s
% Output     : CNFRefutation 12.34s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 152 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 430 expanded)
%              Number of equality atoms :   17 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_101,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_81,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_tarski(A_10),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_79,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    k3_xboole_0('#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_83,c_20])).

tff(c_101,plain,(
    ! [D_47,B_48,A_49] :
      ( r2_hidden(D_47,B_48)
      | ~ r2_hidden(D_47,k3_xboole_0(A_49,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [D_47] :
      ( r2_hidden(D_47,u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_47,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_101])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2059,plain,(
    ! [A_241,B_242,C_243] :
      ( k9_subset_1(u1_struct_0(A_241),B_242,k2_pre_topc(A_241,C_243)) = C_243
      | ~ r1_tarski(C_243,B_242)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ v2_tex_2(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15041,plain,(
    ! [A_658,B_659,A_660] :
      ( k9_subset_1(u1_struct_0(A_658),B_659,k2_pre_topc(A_658,A_660)) = A_660
      | ~ r1_tarski(A_660,B_659)
      | ~ v2_tex_2(B_659,A_658)
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0(A_658)))
      | ~ l1_pre_topc(A_658)
      | ~ v2_pre_topc(A_658)
      | v2_struct_0(A_658)
      | ~ r1_tarski(A_660,u1_struct_0(A_658)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2059])).

tff(c_15048,plain,(
    ! [A_660] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_660)) = A_660
      | ~ r1_tarski(A_660,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_660,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_52,c_15041])).

tff(c_15053,plain,(
    ! [A_660] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_660)) = A_660
      | ~ r1_tarski(A_660,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_660,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_15048])).

tff(c_15055,plain,(
    ! [A_661] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_661)) = A_661
      | ~ r1_tarski(A_661,'#skF_5')
      | ~ r1_tarski(A_661,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_15053])).

tff(c_106,plain,(
    ! [C_51,B_52,A_53] :
      ( ~ v1_xboole_0(C_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_51))
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_53,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_106])).

tff(c_113,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_141,plain,(
    ! [A_60,B_61] :
      ( k6_domain_1(A_60,B_61) = k1_tarski(B_61)
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_155,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_150])).

tff(c_44,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_156,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_44])).

tff(c_15084,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15055,c_156])).

tff(c_15088,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_15084])).

tff(c_15092,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_15088])).

tff(c_15095,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_15092])).

tff(c_15099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_15095])).

tff(c_15100,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_15084])).

tff(c_15104,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_15100])).

tff(c_15108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_15104])).

tff(c_15109,plain,(
    ! [A_53] : ~ r2_hidden(A_53,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_15112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15109,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.23/5.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/5.14  
% 12.34/5.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/5.14  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 12.34/5.14  
% 12.34/5.14  %Foreground sorts:
% 12.34/5.14  
% 12.34/5.14  
% 12.34/5.14  %Background operators:
% 12.34/5.14  
% 12.34/5.14  
% 12.34/5.14  %Foreground operators:
% 12.34/5.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.34/5.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.34/5.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.34/5.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.34/5.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.34/5.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.34/5.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.34/5.14  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 12.34/5.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.34/5.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.34/5.14  tff('#skF_5', type, '#skF_5': $i).
% 12.34/5.14  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 12.34/5.14  tff('#skF_6', type, '#skF_6': $i).
% 12.34/5.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.34/5.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.34/5.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.34/5.14  tff('#skF_4', type, '#skF_4': $i).
% 12.34/5.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.34/5.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.34/5.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.34/5.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.34/5.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.34/5.14  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.34/5.14  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.34/5.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.34/5.14  
% 12.34/5.15  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 12.34/5.15  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 12.34/5.15  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.34/5.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.34/5.15  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 12.34/5.15  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 12.34/5.15  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 12.34/5.15  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 12.34/5.15  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_26, plain, (![A_10, B_11]: (r1_tarski(k1_tarski(A_10), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.34/5.15  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_79, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.34/5.15  tff(c_83, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_79])).
% 12.34/5.15  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.34/5.15  tff(c_87, plain, (k3_xboole_0('#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_83, c_20])).
% 12.34/5.15  tff(c_101, plain, (![D_47, B_48, A_49]: (r2_hidden(D_47, B_48) | ~r2_hidden(D_47, k3_xboole_0(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.34/5.15  tff(c_104, plain, (![D_47]: (r2_hidden(D_47, u1_struct_0('#skF_4')) | ~r2_hidden(D_47, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_101])).
% 12.34/5.15  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_50, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_30, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.34/5.15  tff(c_2059, plain, (![A_241, B_242, C_243]: (k9_subset_1(u1_struct_0(A_241), B_242, k2_pre_topc(A_241, C_243))=C_243 | ~r1_tarski(C_243, B_242) | ~m1_subset_1(C_243, k1_zfmisc_1(u1_struct_0(A_241))) | ~v2_tex_2(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.34/5.15  tff(c_15041, plain, (![A_658, B_659, A_660]: (k9_subset_1(u1_struct_0(A_658), B_659, k2_pre_topc(A_658, A_660))=A_660 | ~r1_tarski(A_660, B_659) | ~v2_tex_2(B_659, A_658) | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0(A_658))) | ~l1_pre_topc(A_658) | ~v2_pre_topc(A_658) | v2_struct_0(A_658) | ~r1_tarski(A_660, u1_struct_0(A_658)))), inference(resolution, [status(thm)], [c_30, c_2059])).
% 12.34/5.15  tff(c_15048, plain, (![A_660]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_660))=A_660 | ~r1_tarski(A_660, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_660, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_52, c_15041])).
% 12.34/5.15  tff(c_15053, plain, (![A_660]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_660))=A_660 | ~r1_tarski(A_660, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_660, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_15048])).
% 12.34/5.15  tff(c_15055, plain, (![A_661]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_661))=A_661 | ~r1_tarski(A_661, '#skF_5') | ~r1_tarski(A_661, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_15053])).
% 12.34/5.15  tff(c_106, plain, (![C_51, B_52, A_53]: (~v1_xboole_0(C_51) | ~m1_subset_1(B_52, k1_zfmisc_1(C_51)) | ~r2_hidden(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.34/5.15  tff(c_112, plain, (![A_53]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_53, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_106])).
% 12.34/5.15  tff(c_113, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_112])).
% 12.34/5.15  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_141, plain, (![A_60, B_61]: (k6_domain_1(A_60, B_61)=k1_tarski(B_61) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.34/5.15  tff(c_150, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_141])).
% 12.34/5.15  tff(c_155, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_113, c_150])).
% 12.34/5.15  tff(c_44, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.34/5.15  tff(c_156, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_44])).
% 12.34/5.15  tff(c_15084, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_15055, c_156])).
% 12.34/5.15  tff(c_15088, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_15084])).
% 12.34/5.16  tff(c_15092, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_15088])).
% 12.34/5.16  tff(c_15095, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_104, c_15092])).
% 12.34/5.16  tff(c_15099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_15095])).
% 12.34/5.16  tff(c_15100, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_15084])).
% 12.34/5.16  tff(c_15104, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_15100])).
% 12.34/5.16  tff(c_15108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_15104])).
% 12.34/5.16  tff(c_15109, plain, (![A_53]: (~r2_hidden(A_53, '#skF_5'))), inference(splitRight, [status(thm)], [c_112])).
% 12.34/5.16  tff(c_15112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15109, c_46])).
% 12.34/5.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/5.16  
% 12.34/5.16  Inference rules
% 12.34/5.16  ----------------------
% 12.34/5.16  #Ref     : 0
% 12.34/5.16  #Sup     : 4502
% 12.34/5.16  #Fact    : 0
% 12.34/5.16  #Define  : 0
% 12.34/5.16  #Split   : 10
% 12.34/5.16  #Chain   : 0
% 12.34/5.16  #Close   : 0
% 12.34/5.16  
% 12.34/5.16  Ordering : KBO
% 12.34/5.16  
% 12.34/5.16  Simplification rules
% 12.34/5.16  ----------------------
% 12.34/5.16  #Subsume      : 1125
% 12.34/5.16  #Demod        : 294
% 12.34/5.16  #Tautology    : 132
% 12.34/5.16  #SimpNegUnit  : 10
% 12.34/5.16  #BackRed      : 3
% 12.34/5.16  
% 12.34/5.16  #Partial instantiations: 0
% 12.34/5.16  #Strategies tried      : 1
% 12.34/5.16  
% 12.34/5.16  Timing (in seconds)
% 12.34/5.16  ----------------------
% 12.34/5.16  Preprocessing        : 0.38
% 12.34/5.16  Parsing              : 0.18
% 12.34/5.16  CNF conversion       : 0.03
% 12.34/5.16  Main loop            : 3.94
% 12.34/5.16  Inferencing          : 0.74
% 12.34/5.16  Reduction            : 0.65
% 12.34/5.16  Demodulation         : 0.43
% 12.34/5.16  BG Simplification    : 0.14
% 12.34/5.16  Subsumption          : 2.17
% 12.34/5.16  Abstraction          : 0.27
% 12.34/5.16  MUC search           : 0.00
% 12.34/5.16  Cooper               : 0.00
% 12.34/5.16  Total                : 4.35
% 12.34/5.16  Index Insertion      : 0.00
% 12.34/5.16  Index Deletion       : 0.00
% 12.34/5.16  Index Matching       : 0.00
% 12.34/5.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
