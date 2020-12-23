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
% DateTime   : Thu Dec  3 10:29:40 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 154 expanded)
%              Number of leaves         :   31 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 428 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_110,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_49,plain,(
    ! [B_32,A_33] :
      ( ~ r2_hidden(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_104,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(B_44,A_45)
      | ~ r2_hidden(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,
    ( m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_104])).

tff(c_114,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_110])).

tff(c_213,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_219,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_213])).

tff(c_235,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_219])).

tff(c_309,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k6_domain_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_333,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_309])).

tff(c_345,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_333])).

tff(c_346,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_345])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_362,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_18])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_73,plain,(
    ! [B_38,A_39] :
      ( v1_xboole_0(B_38)
      | ~ m1_subset_1(B_38,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_93,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_231,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_213])).

tff(c_243,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_231])).

tff(c_330,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_309])).

tff(c_342,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_330])).

tff(c_343,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_342])).

tff(c_953,plain,(
    ! [A_97,B_98,C_99] :
      ( k9_subset_1(u1_struct_0(A_97),B_98,k2_pre_topc(A_97,C_99)) = C_99
      | ~ r1_tarski(C_99,B_98)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_957,plain,(
    ! [B_98] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_98,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_98)
      | ~ v2_tex_2(B_98,'#skF_3')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_343,c_953])).

tff(c_975,plain,(
    ! [B_98] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_98,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_98)
      | ~ v2_tex_2(B_98,'#skF_3')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_957])).

tff(c_1353,plain,(
    ! [B_117] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_117,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_117)
      | ~ v2_tex_2(B_117,'#skF_3')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_975])).

tff(c_34,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_248,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_243,c_34])).

tff(c_1359,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_248])).

tff(c_1367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_362,c_1359])).

tff(c_1369,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1418,plain,(
    ! [C_130,A_131,B_132] :
      ( r2_hidden(C_130,A_131)
      | ~ r2_hidden(C_130,B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1428,plain,(
    ! [A_133] :
      ( r2_hidden('#skF_5',A_133)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1418])).

tff(c_1441,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_1428])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1449,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1441,c_2])).

tff(c_1456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  
% 3.37/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.37/1.57  
% 3.37/1.57  %Foreground sorts:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Background operators:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Foreground operators:
% 3.37/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.37/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.37/1.57  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.37/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.57  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.37/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.37/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.37/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.37/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.37/1.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.37/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.57  
% 3.37/1.58  tff(f_110, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.37/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.37/1.58  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.37/1.58  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.37/1.58  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.37/1.58  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.37/1.58  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.37/1.58  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.37/1.58  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_40, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_49, plain, (![B_32, A_33]: (~r2_hidden(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.58  tff(c_53, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_49])).
% 3.37/1.58  tff(c_104, plain, (![B_44, A_45]: (m1_subset_1(B_44, A_45) | ~r2_hidden(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.58  tff(c_110, plain, (m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_104])).
% 3.37/1.58  tff(c_114, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_53, c_110])).
% 3.37/1.58  tff(c_213, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.37/1.58  tff(c_219, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_114, c_213])).
% 3.37/1.58  tff(c_235, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_53, c_219])).
% 3.37/1.58  tff(c_309, plain, (![A_73, B_74]: (m1_subset_1(k6_domain_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.37/1.58  tff(c_333, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_235, c_309])).
% 3.37/1.58  tff(c_345, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_333])).
% 3.37/1.58  tff(c_346, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_53, c_345])).
% 3.37/1.58  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.37/1.58  tff(c_362, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_346, c_18])).
% 3.37/1.58  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_38, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_73, plain, (![B_38, A_39]: (v1_xboole_0(B_38) | ~m1_subset_1(B_38, A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.58  tff(c_83, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_73])).
% 3.37/1.58  tff(c_93, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_83])).
% 3.37/1.58  tff(c_231, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_213])).
% 3.37/1.58  tff(c_243, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_93, c_231])).
% 3.37/1.58  tff(c_330, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_243, c_309])).
% 3.37/1.58  tff(c_342, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_330])).
% 3.37/1.58  tff(c_343, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_93, c_342])).
% 3.37/1.58  tff(c_953, plain, (![A_97, B_98, C_99]: (k9_subset_1(u1_struct_0(A_97), B_98, k2_pre_topc(A_97, C_99))=C_99 | ~r1_tarski(C_99, B_98) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.37/1.58  tff(c_957, plain, (![B_98]: (k9_subset_1(u1_struct_0('#skF_3'), B_98, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_98) | ~v2_tex_2(B_98, '#skF_3') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_343, c_953])).
% 3.37/1.58  tff(c_975, plain, (![B_98]: (k9_subset_1(u1_struct_0('#skF_3'), B_98, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_98) | ~v2_tex_2(B_98, '#skF_3') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_957])).
% 3.37/1.58  tff(c_1353, plain, (![B_117]: (k9_subset_1(u1_struct_0('#skF_3'), B_117, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_117) | ~v2_tex_2(B_117, '#skF_3') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_975])).
% 3.37/1.58  tff(c_34, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.37/1.58  tff(c_248, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_243, c_34])).
% 3.37/1.58  tff(c_1359, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1353, c_248])).
% 3.37/1.58  tff(c_1367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_362, c_1359])).
% 3.37/1.58  tff(c_1369, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_83])).
% 3.37/1.58  tff(c_1418, plain, (![C_130, A_131, B_132]: (r2_hidden(C_130, A_131) | ~r2_hidden(C_130, B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.58  tff(c_1428, plain, (![A_133]: (r2_hidden('#skF_5', A_133) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_133)))), inference(resolution, [status(thm)], [c_36, c_1418])).
% 3.37/1.58  tff(c_1441, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_1428])).
% 3.37/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.58  tff(c_1449, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1441, c_2])).
% 3.37/1.58  tff(c_1456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1449])).
% 3.37/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.58  
% 3.37/1.58  Inference rules
% 3.37/1.58  ----------------------
% 3.37/1.58  #Ref     : 0
% 3.37/1.58  #Sup     : 300
% 3.37/1.58  #Fact    : 0
% 3.37/1.58  #Define  : 0
% 3.37/1.58  #Split   : 8
% 3.37/1.58  #Chain   : 0
% 3.37/1.58  #Close   : 0
% 3.37/1.58  
% 3.37/1.58  Ordering : KBO
% 3.37/1.58  
% 3.37/1.58  Simplification rules
% 3.37/1.58  ----------------------
% 3.37/1.58  #Subsume      : 42
% 3.37/1.58  #Demod        : 79
% 3.37/1.58  #Tautology    : 96
% 3.37/1.58  #SimpNegUnit  : 101
% 3.37/1.58  #BackRed      : 1
% 3.37/1.58  
% 3.37/1.58  #Partial instantiations: 0
% 3.37/1.58  #Strategies tried      : 1
% 3.37/1.58  
% 3.37/1.58  Timing (in seconds)
% 3.37/1.58  ----------------------
% 3.37/1.59  Preprocessing        : 0.32
% 3.37/1.59  Parsing              : 0.17
% 3.37/1.59  CNF conversion       : 0.02
% 3.37/1.59  Main loop            : 0.46
% 3.37/1.59  Inferencing          : 0.17
% 3.37/1.59  Reduction            : 0.14
% 3.37/1.59  Demodulation         : 0.09
% 3.37/1.59  BG Simplification    : 0.02
% 3.37/1.59  Subsumption          : 0.09
% 3.37/1.59  Abstraction          : 0.03
% 3.37/1.59  MUC search           : 0.00
% 3.37/1.59  Cooper               : 0.00
% 3.37/1.59  Total                : 0.81
% 3.37/1.59  Index Insertion      : 0.00
% 3.37/1.59  Index Deletion       : 0.00
% 3.37/1.59  Index Matching       : 0.00
% 3.37/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
