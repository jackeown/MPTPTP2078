%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 186 expanded)
%              Number of leaves         :   31 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 474 expanded)
%              Number of equality atoms :   13 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k1_tarski(A_38),k1_zfmisc_1(B_39))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tarski(A_38),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_64,c_14])).

tff(c_71,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_44] : r1_tarski(A_44,A_44) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_55,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_122,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_63,c_122])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_320,plain,(
    ! [A_88,A_89] :
      ( r1_tarski(A_88,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_88,A_89)
      | ~ r1_tarski(A_89,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_375,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k1_tarski(A_95),u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_96,'#skF_4')
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_68,c_320])).

tff(c_385,plain,
    ( r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_375])).

tff(c_392,plain,(
    r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_385])).

tff(c_78,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_5',B_48)
      | ~ r1_tarski('#skF_4',B_48) ) ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_302,plain,(
    ! [A_83,B_84,A_85] :
      ( r1_tarski(A_83,B_84)
      | ~ r1_tarski(A_83,k1_tarski(A_85))
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_68,c_122])).

tff(c_466,plain,(
    ! [A_102,B_103,A_104] :
      ( r1_tarski(k1_tarski(A_102),B_103)
      | ~ r2_hidden(A_104,B_103)
      | ~ r2_hidden(A_102,k1_tarski(A_104)) ) ),
    inference(resolution,[status(thm)],[c_68,c_302])).

tff(c_497,plain,(
    ! [A_107] :
      ( r1_tarski(k1_tarski(A_107),'#skF_4')
      | ~ r2_hidden(A_107,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_32,c_466])).

tff(c_551,plain,(
    ! [B_111] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_5'),B_111)),'#skF_4')
      | r1_tarski(k1_tarski('#skF_5'),B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_497])).

tff(c_1017,plain,(
    ! [A_158,B_159] :
      ( r1_tarski(A_158,'#skF_4')
      | ~ r1_tarski(A_158,k1_tarski('#skF_1'(k1_tarski('#skF_5'),B_159)))
      | r1_tarski(k1_tarski('#skF_5'),B_159) ) ),
    inference(resolution,[status(thm)],[c_551,c_8])).

tff(c_1388,plain,(
    ! [A_186,B_187] :
      ( r1_tarski(k1_tarski(A_186),'#skF_4')
      | r1_tarski(k1_tarski('#skF_5'),B_187)
      | ~ r2_hidden(A_186,k1_tarski('#skF_1'(k1_tarski('#skF_5'),B_187))) ) ),
    inference(resolution,[status(thm)],[c_68,c_1017])).

tff(c_1412,plain,(
    ! [B_187] :
      ( r1_tarski(k1_tarski('#skF_5'),'#skF_4')
      | r1_tarski(k1_tarski('#skF_5'),B_187)
      | ~ r1_tarski('#skF_4',k1_tarski('#skF_1'(k1_tarski('#skF_5'),B_187))) ) ),
    inference(resolution,[status(thm)],[c_84,c_1388])).

tff(c_1414,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1412])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_748,plain,(
    ! [A_136,B_137,C_138] :
      ( k9_subset_1(u1_struct_0(A_136),B_137,k2_pre_topc(A_136,C_138)) = C_138
      | ~ r1_tarski(C_138,B_137)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v2_tex_2(B_137,A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2704,plain,(
    ! [A_262,B_263,A_264] :
      ( k9_subset_1(u1_struct_0(A_262),B_263,k2_pre_topc(A_262,A_264)) = A_264
      | ~ r1_tarski(A_264,B_263)
      | ~ v2_tex_2(B_263,A_262)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ r1_tarski(A_264,u1_struct_0(A_262)) ) ),
    inference(resolution,[status(thm)],[c_16,c_748])).

tff(c_2714,plain,(
    ! [A_264] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_264)) = A_264
      | ~ r1_tarski(A_264,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_264,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_2704])).

tff(c_2720,plain,(
    ! [A_264] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_264)) = A_264
      | ~ r1_tarski(A_264,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_264,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_2714])).

tff(c_2722,plain,(
    ! [A_265] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_265)) = A_265
      | ~ r1_tarski(A_265,'#skF_4')
      | ~ r1_tarski(A_265,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2720])).

tff(c_111,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ v1_xboole_0(C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_56,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_121,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_252,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_264,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_252])).

tff(c_270,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_264])).

tff(c_30,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_271,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_270,c_30])).

tff(c_2739,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2722,c_271])).

tff(c_2764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_1414,c_2739])).

tff(c_2766,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1412])).

tff(c_2772,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2766])).

tff(c_2777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2772])).

tff(c_2778,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_2781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2778,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:45:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.91  
% 5.12/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.91  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.12/1.91  
% 5.12/1.91  %Foreground sorts:
% 5.12/1.91  
% 5.12/1.91  
% 5.12/1.91  %Background operators:
% 5.12/1.91  
% 5.12/1.91  
% 5.12/1.91  %Foreground operators:
% 5.12/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.12/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.12/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.12/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.12/1.91  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.12/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.12/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.12/1.91  tff('#skF_5', type, '#skF_5': $i).
% 5.12/1.91  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.12/1.91  tff('#skF_3', type, '#skF_3': $i).
% 5.12/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.12/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/1.91  tff('#skF_4', type, '#skF_4': $i).
% 5.12/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.12/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.12/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.12/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.12/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.12/1.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.12/1.91  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.12/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.12/1.91  
% 5.12/1.93  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 5.12/1.93  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.12/1.93  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.12/1.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.12/1.93  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.12/1.93  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 5.12/1.93  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.12/1.93  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.12/1.93  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_64, plain, (![A_38, B_39]: (m1_subset_1(k1_tarski(A_38), k1_zfmisc_1(B_39)) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.12/1.93  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.12/1.93  tff(c_68, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), B_39) | ~r2_hidden(A_38, B_39))), inference(resolution, [status(thm)], [c_64, c_14])).
% 5.12/1.93  tff(c_71, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.12/1.93  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.12/1.93  tff(c_76, plain, (![A_44]: (r1_tarski(A_44, A_44))), inference(resolution, [status(thm)], [c_71, c_4])).
% 5.12/1.93  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_55, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.12/1.93  tff(c_63, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_55])).
% 5.12/1.93  tff(c_122, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.12/1.93  tff(c_132, plain, (![A_60]: (r1_tarski(A_60, u1_struct_0('#skF_3')) | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_63, c_122])).
% 5.12/1.93  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.12/1.93  tff(c_320, plain, (![A_88, A_89]: (r1_tarski(A_88, u1_struct_0('#skF_3')) | ~r1_tarski(A_88, A_89) | ~r1_tarski(A_89, '#skF_4'))), inference(resolution, [status(thm)], [c_132, c_8])).
% 5.12/1.93  tff(c_375, plain, (![A_95, B_96]: (r1_tarski(k1_tarski(A_95), u1_struct_0('#skF_3')) | ~r1_tarski(B_96, '#skF_4') | ~r2_hidden(A_95, B_96))), inference(resolution, [status(thm)], [c_68, c_320])).
% 5.12/1.93  tff(c_385, plain, (r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_375])).
% 5.12/1.93  tff(c_392, plain, (r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_385])).
% 5.12/1.93  tff(c_78, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.12/1.93  tff(c_84, plain, (![B_48]: (r2_hidden('#skF_5', B_48) | ~r1_tarski('#skF_4', B_48))), inference(resolution, [status(thm)], [c_32, c_78])).
% 5.12/1.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.12/1.93  tff(c_302, plain, (![A_83, B_84, A_85]: (r1_tarski(A_83, B_84) | ~r1_tarski(A_83, k1_tarski(A_85)) | ~r2_hidden(A_85, B_84))), inference(resolution, [status(thm)], [c_68, c_122])).
% 5.12/1.93  tff(c_466, plain, (![A_102, B_103, A_104]: (r1_tarski(k1_tarski(A_102), B_103) | ~r2_hidden(A_104, B_103) | ~r2_hidden(A_102, k1_tarski(A_104)))), inference(resolution, [status(thm)], [c_68, c_302])).
% 5.12/1.93  tff(c_497, plain, (![A_107]: (r1_tarski(k1_tarski(A_107), '#skF_4') | ~r2_hidden(A_107, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_32, c_466])).
% 5.12/1.93  tff(c_551, plain, (![B_111]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_5'), B_111)), '#skF_4') | r1_tarski(k1_tarski('#skF_5'), B_111))), inference(resolution, [status(thm)], [c_6, c_497])).
% 5.12/1.93  tff(c_1017, plain, (![A_158, B_159]: (r1_tarski(A_158, '#skF_4') | ~r1_tarski(A_158, k1_tarski('#skF_1'(k1_tarski('#skF_5'), B_159))) | r1_tarski(k1_tarski('#skF_5'), B_159))), inference(resolution, [status(thm)], [c_551, c_8])).
% 5.12/1.93  tff(c_1388, plain, (![A_186, B_187]: (r1_tarski(k1_tarski(A_186), '#skF_4') | r1_tarski(k1_tarski('#skF_5'), B_187) | ~r2_hidden(A_186, k1_tarski('#skF_1'(k1_tarski('#skF_5'), B_187))))), inference(resolution, [status(thm)], [c_68, c_1017])).
% 5.12/1.93  tff(c_1412, plain, (![B_187]: (r1_tarski(k1_tarski('#skF_5'), '#skF_4') | r1_tarski(k1_tarski('#skF_5'), B_187) | ~r1_tarski('#skF_4', k1_tarski('#skF_1'(k1_tarski('#skF_5'), B_187))))), inference(resolution, [status(thm)], [c_84, c_1388])).
% 5.12/1.93  tff(c_1414, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1412])).
% 5.12/1.93  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.12/1.93  tff(c_748, plain, (![A_136, B_137, C_138]: (k9_subset_1(u1_struct_0(A_136), B_137, k2_pre_topc(A_136, C_138))=C_138 | ~r1_tarski(C_138, B_137) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_136))) | ~v2_tex_2(B_137, A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.12/1.93  tff(c_2704, plain, (![A_262, B_263, A_264]: (k9_subset_1(u1_struct_0(A_262), B_263, k2_pre_topc(A_262, A_264))=A_264 | ~r1_tarski(A_264, B_263) | ~v2_tex_2(B_263, A_262) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262) | ~r1_tarski(A_264, u1_struct_0(A_262)))), inference(resolution, [status(thm)], [c_16, c_748])).
% 5.12/1.93  tff(c_2714, plain, (![A_264]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_264))=A_264 | ~r1_tarski(A_264, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_264, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_2704])).
% 5.12/1.93  tff(c_2720, plain, (![A_264]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_264))=A_264 | ~r1_tarski(A_264, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_264, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_2714])).
% 5.12/1.93  tff(c_2722, plain, (![A_265]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_265))=A_265 | ~r1_tarski(A_265, '#skF_4') | ~r1_tarski(A_265, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_2720])).
% 5.12/1.93  tff(c_111, plain, (![C_54, B_55, A_56]: (~v1_xboole_0(C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.12/1.93  tff(c_120, plain, (![A_56]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_56, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_111])).
% 5.12/1.93  tff(c_121, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_120])).
% 5.12/1.93  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_252, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.12/1.93  tff(c_264, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_252])).
% 5.12/1.93  tff(c_270, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_121, c_264])).
% 5.12/1.93  tff(c_30, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.12/1.93  tff(c_271, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_270, c_30])).
% 5.12/1.93  tff(c_2739, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2722, c_271])).
% 5.12/1.93  tff(c_2764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_392, c_1414, c_2739])).
% 5.12/1.93  tff(c_2766, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1412])).
% 5.12/1.93  tff(c_2772, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_2766])).
% 5.12/1.93  tff(c_2777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_2772])).
% 5.12/1.93  tff(c_2778, plain, (![A_56]: (~r2_hidden(A_56, '#skF_4'))), inference(splitRight, [status(thm)], [c_120])).
% 5.12/1.93  tff(c_2781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2778, c_32])).
% 5.12/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.93  
% 5.12/1.93  Inference rules
% 5.12/1.93  ----------------------
% 5.12/1.93  #Ref     : 0
% 5.12/1.93  #Sup     : 715
% 5.12/1.93  #Fact    : 0
% 5.12/1.93  #Define  : 0
% 5.12/1.93  #Split   : 7
% 5.12/1.93  #Chain   : 0
% 5.12/1.93  #Close   : 0
% 5.12/1.93  
% 5.12/1.93  Ordering : KBO
% 5.12/1.93  
% 5.12/1.93  Simplification rules
% 5.12/1.93  ----------------------
% 5.12/1.93  #Subsume      : 325
% 5.12/1.93  #Demod        : 98
% 5.12/1.93  #Tautology    : 79
% 5.12/1.93  #SimpNegUnit  : 7
% 5.12/1.93  #BackRed      : 2
% 5.12/1.93  
% 5.12/1.93  #Partial instantiations: 0
% 5.12/1.93  #Strategies tried      : 1
% 5.12/1.93  
% 5.12/1.93  Timing (in seconds)
% 5.12/1.93  ----------------------
% 5.12/1.93  Preprocessing        : 0.31
% 5.12/1.93  Parsing              : 0.16
% 5.12/1.93  CNF conversion       : 0.02
% 5.12/1.93  Main loop            : 0.85
% 5.12/1.93  Inferencing          : 0.26
% 5.12/1.93  Reduction            : 0.25
% 5.12/1.93  Demodulation         : 0.17
% 5.12/1.93  BG Simplification    : 0.03
% 5.12/1.93  Subsumption          : 0.26
% 5.12/1.93  Abstraction          : 0.04
% 5.12/1.93  MUC search           : 0.00
% 5.12/1.93  Cooper               : 0.00
% 5.12/1.93  Total                : 1.20
% 5.12/1.93  Index Insertion      : 0.00
% 5.12/1.93  Index Deletion       : 0.00
% 5.12/1.93  Index Matching       : 0.00
% 5.12/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
