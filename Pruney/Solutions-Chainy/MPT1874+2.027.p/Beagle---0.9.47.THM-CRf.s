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
% DateTime   : Thu Dec  3 10:29:40 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 164 expanded)
%              Number of leaves         :   38 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 434 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_122,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,(
    ! [B_61,A_62] :
      ( ~ r2_hidden(B_61,A_62)
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_74])).

tff(c_151,plain,(
    ! [B_81,A_82] :
      ( m1_subset_1(B_81,A_82)
      | ~ r2_hidden(B_81,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_163,plain,
    ( m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_151])).

tff(c_169,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_163])).

tff(c_326,plain,(
    ! [A_106,B_107] :
      ( k6_domain_1(A_106,B_107) = k1_tarski(B_107)
      | ~ m1_subset_1(B_107,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_332,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_326])).

tff(c_348,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_332])).

tff(c_419,plain,(
    ! [A_117,B_118] :
      ( m1_subset_1(k6_domain_1(A_117,B_118),k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,A_117)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_440,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_419])).

tff(c_451,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_440])).

tff(c_452,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_451])).

tff(c_34,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_464,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_452,c_34])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_104,plain,(
    ! [B_70,A_71] :
      ( v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_118,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_104])).

tff(c_119,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_344,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_326])).

tff(c_356,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_344])).

tff(c_437,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_419])).

tff(c_448,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_437])).

tff(c_449,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_448])).

tff(c_1369,plain,(
    ! [A_183,B_184,C_185] :
      ( k9_subset_1(u1_struct_0(A_183),B_184,k2_pre_topc(A_183,C_185)) = C_185
      | ~ r1_tarski(C_185,B_184)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ v2_tex_2(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1376,plain,(
    ! [B_184] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_184,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_184)
      | ~ v2_tex_2(B_184,'#skF_4')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_449,c_1369])).

tff(c_1398,plain,(
    ! [B_184] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_184,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_184)
      | ~ v2_tex_2(B_184,'#skF_4')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1376])).

tff(c_1923,plain,(
    ! [B_194] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_194,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_194)
      | ~ v2_tex_2(B_194,'#skF_4')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1398])).

tff(c_50,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_370,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_356,c_50])).

tff(c_1929,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_370])).

tff(c_1937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_464,c_1929])).

tff(c_1939,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_84,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_88,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_84])).

tff(c_2017,plain,(
    ! [C_215,B_216,A_217] :
      ( r2_hidden(C_215,B_216)
      | ~ r2_hidden(C_215,A_217)
      | ~ r1_tarski(A_217,B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2030,plain,(
    ! [B_218] :
      ( r2_hidden('#skF_6',B_218)
      | ~ r1_tarski('#skF_5',B_218) ) ),
    inference(resolution,[status(thm)],[c_52,c_2017])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2042,plain,(
    ! [B_219] :
      ( ~ v1_xboole_0(B_219)
      | ~ r1_tarski('#skF_5',B_219) ) ),
    inference(resolution,[status(thm)],[c_2030,c_2])).

tff(c_2053,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_2042])).

tff(c_2059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_2053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:01:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.53  
% 5.99/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.53  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.99/2.53  
% 5.99/2.53  %Foreground sorts:
% 5.99/2.53  
% 5.99/2.53  
% 5.99/2.53  %Background operators:
% 5.99/2.53  
% 5.99/2.53  
% 5.99/2.53  %Foreground operators:
% 5.99/2.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.99/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.99/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.99/2.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.99/2.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.99/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.99/2.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.99/2.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.99/2.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.99/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.99/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.99/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.99/2.53  tff('#skF_5', type, '#skF_5': $i).
% 5.99/2.53  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.99/2.53  tff('#skF_6', type, '#skF_6': $i).
% 5.99/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.99/2.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.99/2.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.99/2.53  tff('#skF_4', type, '#skF_4': $i).
% 5.99/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.99/2.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.99/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.99/2.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.99/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.99/2.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.99/2.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.99/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.99/2.53  
% 5.99/2.55  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 5.99/2.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.99/2.55  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.99/2.55  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.99/2.55  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.99/2.55  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.99/2.55  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 5.99/2.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.99/2.55  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_56, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_52, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_74, plain, (![B_61, A_62]: (~r2_hidden(B_61, A_62) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.55  tff(c_78, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_74])).
% 5.99/2.55  tff(c_151, plain, (![B_81, A_82]: (m1_subset_1(B_81, A_82) | ~r2_hidden(B_81, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.99/2.55  tff(c_163, plain, (m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_151])).
% 5.99/2.55  tff(c_169, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_163])).
% 5.99/2.55  tff(c_326, plain, (![A_106, B_107]: (k6_domain_1(A_106, B_107)=k1_tarski(B_107) | ~m1_subset_1(B_107, A_106) | v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.99/2.55  tff(c_332, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_169, c_326])).
% 5.99/2.55  tff(c_348, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_332])).
% 5.99/2.55  tff(c_419, plain, (![A_117, B_118]: (m1_subset_1(k6_domain_1(A_117, B_118), k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, A_117) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.99/2.55  tff(c_440, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_348, c_419])).
% 5.99/2.55  tff(c_451, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_440])).
% 5.99/2.55  tff(c_452, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_451])).
% 5.99/2.55  tff(c_34, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.99/2.55  tff(c_464, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_452, c_34])).
% 5.99/2.55  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_104, plain, (![B_70, A_71]: (v1_xboole_0(B_70) | ~m1_subset_1(B_70, A_71) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.99/2.55  tff(c_118, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_104])).
% 5.99/2.55  tff(c_119, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_118])).
% 5.99/2.55  tff(c_344, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_326])).
% 5.99/2.55  tff(c_356, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_119, c_344])).
% 5.99/2.55  tff(c_437, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_356, c_419])).
% 5.99/2.55  tff(c_448, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_437])).
% 5.99/2.55  tff(c_449, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_119, c_448])).
% 5.99/2.55  tff(c_1369, plain, (![A_183, B_184, C_185]: (k9_subset_1(u1_struct_0(A_183), B_184, k2_pre_topc(A_183, C_185))=C_185 | ~r1_tarski(C_185, B_184) | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0(A_183))) | ~v2_tex_2(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.99/2.55  tff(c_1376, plain, (![B_184]: (k9_subset_1(u1_struct_0('#skF_4'), B_184, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_184) | ~v2_tex_2(B_184, '#skF_4') | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_449, c_1369])).
% 5.99/2.55  tff(c_1398, plain, (![B_184]: (k9_subset_1(u1_struct_0('#skF_4'), B_184, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_184) | ~v2_tex_2(B_184, '#skF_4') | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1376])).
% 5.99/2.55  tff(c_1923, plain, (![B_194]: (k9_subset_1(u1_struct_0('#skF_4'), B_194, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_194) | ~v2_tex_2(B_194, '#skF_4') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1398])).
% 5.99/2.55  tff(c_50, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.99/2.55  tff(c_370, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_356, c_50])).
% 5.99/2.55  tff(c_1929, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1923, c_370])).
% 5.99/2.55  tff(c_1937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_464, c_1929])).
% 5.99/2.55  tff(c_1939, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_118])).
% 5.99/2.55  tff(c_84, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.99/2.55  tff(c_88, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_84])).
% 5.99/2.55  tff(c_2017, plain, (![C_215, B_216, A_217]: (r2_hidden(C_215, B_216) | ~r2_hidden(C_215, A_217) | ~r1_tarski(A_217, B_216))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.99/2.55  tff(c_2030, plain, (![B_218]: (r2_hidden('#skF_6', B_218) | ~r1_tarski('#skF_5', B_218))), inference(resolution, [status(thm)], [c_52, c_2017])).
% 5.99/2.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.55  tff(c_2042, plain, (![B_219]: (~v1_xboole_0(B_219) | ~r1_tarski('#skF_5', B_219))), inference(resolution, [status(thm)], [c_2030, c_2])).
% 5.99/2.55  tff(c_2053, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_2042])).
% 5.99/2.55  tff(c_2059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1939, c_2053])).
% 5.99/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.55  
% 5.99/2.55  Inference rules
% 5.99/2.55  ----------------------
% 5.99/2.55  #Ref     : 0
% 5.99/2.55  #Sup     : 436
% 5.99/2.55  #Fact    : 0
% 5.99/2.55  #Define  : 0
% 5.99/2.55  #Split   : 12
% 5.99/2.55  #Chain   : 0
% 5.99/2.55  #Close   : 0
% 5.99/2.55  
% 5.99/2.55  Ordering : KBO
% 5.99/2.55  
% 5.99/2.55  Simplification rules
% 5.99/2.56  ----------------------
% 5.99/2.56  #Subsume      : 79
% 5.99/2.56  #Demod        : 112
% 5.99/2.56  #Tautology    : 137
% 5.99/2.56  #SimpNegUnit  : 115
% 5.99/2.56  #BackRed      : 1
% 5.99/2.56  
% 5.99/2.56  #Partial instantiations: 0
% 5.99/2.56  #Strategies tried      : 1
% 5.99/2.56  
% 5.99/2.56  Timing (in seconds)
% 5.99/2.56  ----------------------
% 5.99/2.56  Preprocessing        : 0.55
% 5.99/2.56  Parsing              : 0.28
% 5.99/2.56  CNF conversion       : 0.04
% 5.99/2.56  Main loop            : 1.10
% 5.99/2.56  Inferencing          : 0.40
% 5.99/2.56  Reduction            : 0.34
% 5.99/2.56  Demodulation         : 0.22
% 5.99/2.56  BG Simplification    : 0.05
% 5.99/2.56  Subsumption          : 0.23
% 5.99/2.56  Abstraction          : 0.05
% 5.99/2.56  MUC search           : 0.00
% 5.99/2.56  Cooper               : 0.00
% 5.99/2.56  Total                : 1.71
% 5.99/2.56  Index Insertion      : 0.00
% 5.99/2.56  Index Deletion       : 0.00
% 5.99/2.56  Index Matching       : 0.00
% 5.99/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
