%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:40 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 159 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 460 expanded)
%              Number of equality atoms :   15 (  47 expanded)
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

tff(f_108,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_88,axiom,(
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

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_85,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(B_37,A_38)
      | ~ r2_hidden(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,
    ( m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_90,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ v1_xboole_0(C_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    ! [B_50,A_51,A_52] :
      ( ~ v1_xboole_0(B_50)
      | ~ r2_hidden(A_51,A_52)
      | ~ r1_tarski(A_52,B_50) ) ),
    inference(resolution,[status(thm)],[c_18,c_109])).

tff(c_128,plain,(
    ! [B_53] :
      ( ~ v1_xboole_0(B_53)
      | ~ r1_tarski('#skF_3',B_53) ) ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_135,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_135])).

tff(c_142,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_141,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_194,plain,(
    ! [A_69,B_70] :
      ( k6_domain_1(A_69,B_70) = k1_tarski(B_70)
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_197,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_194])).

tff(c_212,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_197])).

tff(c_230,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k6_domain_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_247,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_230])).

tff(c_256,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_247])).

tff(c_257,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_256])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_272,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_257,c_16])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_67,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_84,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_209,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_194])).

tff(c_220,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_209])).

tff(c_244,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_230])).

tff(c_253,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_244])).

tff(c_254,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_253])).

tff(c_537,plain,(
    ! [A_85,B_86,C_87] :
      ( k9_subset_1(u1_struct_0(A_85),B_86,k2_pre_topc(A_85,C_87)) = C_87
      | ~ r1_tarski(C_87,B_86)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_541,plain,(
    ! [B_86] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_86,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_86)
      | ~ v2_tex_2(B_86,'#skF_2')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_254,c_537])).

tff(c_556,plain,(
    ! [B_86] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_86,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_86)
      | ~ v2_tex_2(B_86,'#skF_2')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_541])).

tff(c_1091,plain,(
    ! [B_99] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_99,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_99)
      | ~ v2_tex_2(B_99,'#skF_2')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_556])).

tff(c_34,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_225,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_220,c_34])).

tff(c_1097,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_225])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_272,c_1097])).

tff(c_1107,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1133,plain,(
    ! [C_110,B_111,A_112] :
      ( ~ v1_xboole_0(C_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(C_110))
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1140,plain,(
    ! [A_112] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_112,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_1133])).

tff(c_1145,plain,(
    ! [A_112] : ~ r2_hidden(A_112,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1140])).

tff(c_1147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1145,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:45:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/2.11  
% 4.16/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/2.11  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.16/2.11  
% 4.16/2.11  %Foreground sorts:
% 4.16/2.11  
% 4.16/2.11  
% 4.16/2.11  %Background operators:
% 4.16/2.11  
% 4.16/2.11  
% 4.16/2.11  %Foreground operators:
% 4.16/2.11  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.16/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/2.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.16/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.16/2.11  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.16/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/2.11  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.16/2.11  tff('#skF_2', type, '#skF_2': $i).
% 4.16/2.11  tff('#skF_3', type, '#skF_3': $i).
% 4.16/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/2.11  tff('#skF_4', type, '#skF_4': $i).
% 4.16/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.16/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.16/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.16/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/2.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.16/2.11  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.16/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/2.11  
% 4.43/2.14  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.43/2.14  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.43/2.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.43/2.14  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.43/2.14  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.43/2.14  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.43/2.14  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.43/2.14  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.43/2.14  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_40, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_85, plain, (![B_37, A_38]: (m1_subset_1(B_37, A_38) | ~r2_hidden(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.43/2.14  tff(c_89, plain, (m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_85])).
% 4.43/2.14  tff(c_90, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_89])).
% 4.43/2.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.43/2.14  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.43/2.14  tff(c_109, plain, (![C_45, B_46, A_47]: (~v1_xboole_0(C_45) | ~m1_subset_1(B_46, k1_zfmisc_1(C_45)) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.43/2.14  tff(c_121, plain, (![B_50, A_51, A_52]: (~v1_xboole_0(B_50) | ~r2_hidden(A_51, A_52) | ~r1_tarski(A_52, B_50))), inference(resolution, [status(thm)], [c_18, c_109])).
% 4.43/2.14  tff(c_128, plain, (![B_53]: (~v1_xboole_0(B_53) | ~r1_tarski('#skF_3', B_53))), inference(resolution, [status(thm)], [c_36, c_121])).
% 4.43/2.14  tff(c_135, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_128])).
% 4.43/2.14  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_135])).
% 4.43/2.14  tff(c_142, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_89])).
% 4.43/2.14  tff(c_141, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_89])).
% 4.43/2.14  tff(c_194, plain, (![A_69, B_70]: (k6_domain_1(A_69, B_70)=k1_tarski(B_70) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.43/2.14  tff(c_197, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_141, c_194])).
% 4.43/2.14  tff(c_212, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_142, c_197])).
% 4.43/2.14  tff(c_230, plain, (![A_71, B_72]: (m1_subset_1(k6_domain_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.43/2.14  tff(c_247, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_212, c_230])).
% 4.43/2.14  tff(c_256, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_247])).
% 4.43/2.14  tff(c_257, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_142, c_256])).
% 4.43/2.14  tff(c_16, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.43/2.14  tff(c_272, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_257, c_16])).
% 4.43/2.14  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_67, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.43/2.14  tff(c_83, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_67])).
% 4.43/2.14  tff(c_84, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_83])).
% 4.43/2.14  tff(c_209, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_194])).
% 4.43/2.14  tff(c_220, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_84, c_209])).
% 4.43/2.14  tff(c_244, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_230])).
% 4.43/2.14  tff(c_253, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_244])).
% 4.43/2.14  tff(c_254, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_84, c_253])).
% 4.43/2.14  tff(c_537, plain, (![A_85, B_86, C_87]: (k9_subset_1(u1_struct_0(A_85), B_86, k2_pre_topc(A_85, C_87))=C_87 | ~r1_tarski(C_87, B_86) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_85))) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.43/2.14  tff(c_541, plain, (![B_86]: (k9_subset_1(u1_struct_0('#skF_2'), B_86, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_86) | ~v2_tex_2(B_86, '#skF_2') | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_254, c_537])).
% 4.43/2.14  tff(c_556, plain, (![B_86]: (k9_subset_1(u1_struct_0('#skF_2'), B_86, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_86) | ~v2_tex_2(B_86, '#skF_2') | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_541])).
% 4.43/2.14  tff(c_1091, plain, (![B_99]: (k9_subset_1(u1_struct_0('#skF_2'), B_99, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_99) | ~v2_tex_2(B_99, '#skF_2') | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_556])).
% 4.43/2.14  tff(c_34, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.43/2.14  tff(c_225, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_220, c_34])).
% 4.43/2.14  tff(c_1097, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_225])).
% 4.43/2.14  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_272, c_1097])).
% 4.43/2.14  tff(c_1107, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_83])).
% 4.43/2.14  tff(c_1133, plain, (![C_110, B_111, A_112]: (~v1_xboole_0(C_110) | ~m1_subset_1(B_111, k1_zfmisc_1(C_110)) | ~r2_hidden(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.43/2.14  tff(c_1140, plain, (![A_112]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_112, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_1133])).
% 4.43/2.14  tff(c_1145, plain, (![A_112]: (~r2_hidden(A_112, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1140])).
% 4.43/2.14  tff(c_1147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1145, c_36])).
% 4.43/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/2.14  
% 4.43/2.14  Inference rules
% 4.43/2.14  ----------------------
% 4.43/2.14  #Ref     : 0
% 4.43/2.14  #Sup     : 237
% 4.43/2.14  #Fact    : 0
% 4.43/2.14  #Define  : 0
% 4.43/2.14  #Split   : 18
% 4.43/2.14  #Chain   : 0
% 4.43/2.14  #Close   : 0
% 4.43/2.14  
% 4.43/2.14  Ordering : KBO
% 4.43/2.14  
% 4.43/2.14  Simplification rules
% 4.43/2.14  ----------------------
% 4.43/2.14  #Subsume      : 46
% 4.43/2.14  #Demod        : 94
% 4.43/2.14  #Tautology    : 79
% 4.43/2.14  #SimpNegUnit  : 67
% 4.43/2.14  #BackRed      : 2
% 4.43/2.14  
% 4.43/2.14  #Partial instantiations: 0
% 4.43/2.14  #Strategies tried      : 1
% 4.43/2.14  
% 4.43/2.14  Timing (in seconds)
% 4.43/2.14  ----------------------
% 4.43/2.14  Preprocessing        : 0.50
% 4.43/2.14  Parsing              : 0.25
% 4.43/2.14  CNF conversion       : 0.04
% 4.43/2.14  Main loop            : 0.71
% 4.43/2.14  Inferencing          : 0.24
% 4.43/2.14  Reduction            : 0.23
% 4.43/2.14  Demodulation         : 0.16
% 4.43/2.14  BG Simplification    : 0.04
% 4.43/2.14  Subsumption          : 0.15
% 4.43/2.14  Abstraction          : 0.04
% 4.43/2.14  MUC search           : 0.00
% 4.43/2.14  Cooper               : 0.00
% 4.43/2.14  Total                : 1.27
% 4.43/2.14  Index Insertion      : 0.00
% 4.43/2.14  Index Deletion       : 0.00
% 4.43/2.14  Index Matching       : 0.00
% 4.43/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
