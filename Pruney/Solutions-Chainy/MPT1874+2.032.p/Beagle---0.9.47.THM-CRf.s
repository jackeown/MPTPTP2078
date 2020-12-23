%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:41 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 152 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 393 expanded)
%              Number of equality atoms :   14 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    ! [B_40,A_41] :
      ( ~ r2_hidden(B_40,A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_66,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_235,plain,(
    ! [A_75,B_76] :
      ( k6_domain_1(A_75,B_76) = k1_tarski(B_76)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_244,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_235])).

tff(c_255,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_244])).

tff(c_327,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k6_domain_1(A_87,B_88),k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_342,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_327])).

tff(c_349,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_342])).

tff(c_350,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_349])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    ! [C_63,A_64,B_65] :
      ( r2_hidden(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_552,plain,(
    ! [A_116,B_117,A_118] :
      ( r2_hidden('#skF_2'(A_116,B_117),A_118)
      | ~ m1_subset_1(A_116,k1_zfmisc_1(A_118))
      | r1_tarski(A_116,B_117) ) ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_572,plain,(
    ! [A_119,A_120] :
      ( ~ m1_subset_1(A_119,k1_zfmisc_1(A_120))
      | r1_tarski(A_119,A_120) ) ),
    inference(resolution,[status(thm)],[c_552,c_8])).

tff(c_612,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_350,c_572])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_178,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_6',A_68)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_38,c_139])).

tff(c_182,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_197,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_250,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_235])).

tff(c_259,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_250])).

tff(c_339,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_327])).

tff(c_346,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_339])).

tff(c_347,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_346])).

tff(c_943,plain,(
    ! [A_140,B_141,C_142] :
      ( k9_subset_1(u1_struct_0(A_140),B_141,k2_pre_topc(A_140,C_142)) = C_142
      | ~ r1_tarski(C_142,B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ v2_tex_2(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_953,plain,(
    ! [B_141] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_141,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_141)
      | ~ v2_tex_2(B_141,'#skF_4')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_347,c_943])).

tff(c_973,plain,(
    ! [B_141] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_141,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_141)
      | ~ v2_tex_2(B_141,'#skF_4')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_953])).

tff(c_1296,plain,(
    ! [B_162] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_162,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_162)
      | ~ v2_tex_2(B_162,'#skF_4')
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_973])).

tff(c_36,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_264,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_259,c_36])).

tff(c_1302,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_264])).

tff(c_1310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_612,c_1302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n007.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:12:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.60  
% 3.50/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.60  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.50/1.60  
% 3.50/1.60  %Foreground sorts:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Background operators:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Foreground operators:
% 3.50/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.50/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.50/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.50/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.50/1.60  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.50/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.50/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.50/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.50/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.50/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.50/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.50/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.50/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.60  
% 3.50/1.61  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.50/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.50/1.61  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.50/1.61  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.50/1.61  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.50/1.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.50/1.61  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.50/1.61  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.50/1.61  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_42, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_52, plain, (![B_40, A_41]: (~r2_hidden(B_40, A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.61  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_52])).
% 3.50/1.61  tff(c_66, plain, (![A_43, B_44]: (m1_subset_1(A_43, B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.50/1.61  tff(c_70, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_66])).
% 3.50/1.61  tff(c_235, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.50/1.61  tff(c_244, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_235])).
% 3.50/1.61  tff(c_255, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_244])).
% 3.50/1.61  tff(c_327, plain, (![A_87, B_88]: (m1_subset_1(k6_domain_1(A_87, B_88), k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.50/1.61  tff(c_342, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_255, c_327])).
% 3.50/1.61  tff(c_349, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_342])).
% 3.50/1.61  tff(c_350, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_349])).
% 3.50/1.61  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.50/1.61  tff(c_139, plain, (![C_63, A_64, B_65]: (r2_hidden(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.50/1.61  tff(c_552, plain, (![A_116, B_117, A_118]: (r2_hidden('#skF_2'(A_116, B_117), A_118) | ~m1_subset_1(A_116, k1_zfmisc_1(A_118)) | r1_tarski(A_116, B_117))), inference(resolution, [status(thm)], [c_10, c_139])).
% 3.50/1.61  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.50/1.61  tff(c_572, plain, (![A_119, A_120]: (~m1_subset_1(A_119, k1_zfmisc_1(A_120)) | r1_tarski(A_119, A_120))), inference(resolution, [status(thm)], [c_552, c_8])).
% 3.50/1.61  tff(c_612, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_350, c_572])).
% 3.50/1.61  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_178, plain, (![A_68]: (r2_hidden('#skF_6', A_68) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_38, c_139])).
% 3.50/1.61  tff(c_182, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_178])).
% 3.50/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.61  tff(c_197, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_182, c_2])).
% 3.50/1.61  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_250, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_235])).
% 3.50/1.61  tff(c_259, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_197, c_250])).
% 3.50/1.61  tff(c_339, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_327])).
% 3.50/1.61  tff(c_346, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_339])).
% 3.50/1.61  tff(c_347, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_197, c_346])).
% 3.50/1.61  tff(c_943, plain, (![A_140, B_141, C_142]: (k9_subset_1(u1_struct_0(A_140), B_141, k2_pre_topc(A_140, C_142))=C_142 | ~r1_tarski(C_142, B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0(A_140))) | ~v2_tex_2(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.50/1.61  tff(c_953, plain, (![B_141]: (k9_subset_1(u1_struct_0('#skF_4'), B_141, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_141) | ~v2_tex_2(B_141, '#skF_4') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_347, c_943])).
% 3.50/1.61  tff(c_973, plain, (![B_141]: (k9_subset_1(u1_struct_0('#skF_4'), B_141, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_141) | ~v2_tex_2(B_141, '#skF_4') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_953])).
% 3.50/1.61  tff(c_1296, plain, (![B_162]: (k9_subset_1(u1_struct_0('#skF_4'), B_162, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_162) | ~v2_tex_2(B_162, '#skF_4') | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_973])).
% 3.50/1.61  tff(c_36, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.50/1.61  tff(c_264, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_259, c_36])).
% 3.50/1.61  tff(c_1302, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1296, c_264])).
% 3.50/1.61  tff(c_1310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_612, c_1302])).
% 3.50/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.61  
% 3.50/1.61  Inference rules
% 3.50/1.61  ----------------------
% 3.50/1.61  #Ref     : 0
% 3.50/1.61  #Sup     : 286
% 3.50/1.61  #Fact    : 0
% 3.50/1.61  #Define  : 0
% 3.50/1.61  #Split   : 4
% 3.50/1.61  #Chain   : 0
% 3.50/1.61  #Close   : 0
% 3.50/1.61  
% 3.50/1.61  Ordering : KBO
% 3.50/1.61  
% 3.50/1.61  Simplification rules
% 3.50/1.61  ----------------------
% 3.50/1.61  #Subsume      : 49
% 3.50/1.61  #Demod        : 60
% 3.50/1.61  #Tautology    : 60
% 3.50/1.61  #SimpNegUnit  : 25
% 3.50/1.61  #BackRed      : 1
% 3.50/1.61  
% 3.50/1.61  #Partial instantiations: 0
% 3.50/1.61  #Strategies tried      : 1
% 3.50/1.61  
% 3.50/1.61  Timing (in seconds)
% 3.50/1.61  ----------------------
% 3.50/1.62  Preprocessing        : 0.33
% 3.50/1.62  Parsing              : 0.18
% 3.50/1.62  CNF conversion       : 0.02
% 3.50/1.62  Main loop            : 0.47
% 3.50/1.62  Inferencing          : 0.17
% 3.50/1.62  Reduction            : 0.13
% 3.50/1.62  Demodulation         : 0.09
% 3.50/1.62  BG Simplification    : 0.02
% 3.50/1.62  Subsumption          : 0.10
% 3.50/1.62  Abstraction          : 0.02
% 3.50/1.62  MUC search           : 0.00
% 3.50/1.62  Cooper               : 0.00
% 3.50/1.62  Total                : 0.84
% 3.50/1.62  Index Insertion      : 0.00
% 3.50/1.62  Index Deletion       : 0.00
% 3.50/1.62  Index Matching       : 0.00
% 3.50/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
