%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:32 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   61 (  95 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 239 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_85,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_88,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [A_43,A_44] :
      ( ~ v1_xboole_0(A_43)
      | ~ r2_hidden(A_44,A_43) ) ),
    inference(resolution,[status(thm)],[c_37,c_88])).

tff(c_99,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    ! [B_65,A_66] :
      ( v2_tex_2(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ v1_xboole_0(B_65)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_160,plain,(
    ! [A_68,A_69] :
      ( v2_tex_2(A_68,A_69)
      | ~ v1_xboole_0(A_68)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69)
      | ~ r1_tarski(A_68,u1_struct_0(A_69)) ) ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_169,plain,(
    ! [A_1,A_69] :
      ( v2_tex_2(A_1,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69)
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_99,c_160])).

tff(c_32,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_200,plain,(
    ! [A_77,B_78] :
      ( v3_tex_2('#skF_2'(A_77,B_78),A_77)
      | ~ v2_tex_2(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v3_tdlat_3(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_277,plain,(
    ! [A_85,A_86] :
      ( v3_tex_2('#skF_2'(A_85,A_86),A_85)
      | ~ v2_tex_2(A_86,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ v3_tdlat_3(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85)
      | ~ r1_tarski(A_86,u1_struct_0(A_85)) ) ),
    inference(resolution,[status(thm)],[c_16,c_200])).

tff(c_219,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1('#skF_2'(A_80,B_81),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v3_tdlat_3(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    ! [B_23] :
      ( ~ v3_tex_2(B_23,'#skF_3')
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_229,plain,(
    ! [B_81] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_81),'#skF_3')
      | ~ v2_tex_2(B_81,'#skF_3')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_219,c_28])).

tff(c_238,plain,(
    ! [B_81] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_81),'#skF_3')
      | ~ v2_tex_2(B_81,'#skF_3')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_229])).

tff(c_248,plain,(
    ! [B_82] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_82),'#skF_3')
      | ~ v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_238])).

tff(c_265,plain,(
    ! [A_8] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',A_8),'#skF_3')
      | ~ v2_tex_2(A_8,'#skF_3')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_248])).

tff(c_281,plain,(
    ! [A_86] :
      ( ~ v2_tex_2(A_86,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_86,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_277,c_265])).

tff(c_291,plain,(
    ! [A_86] :
      ( ~ v2_tex_2(A_86,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_86,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_281])).

tff(c_301,plain,(
    ! [A_87] :
      ( ~ v2_tex_2(A_87,'#skF_3')
      | ~ r1_tarski(A_87,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_291])).

tff(c_312,plain,(
    ! [A_88] :
      ( ~ v2_tex_2(A_88,'#skF_3')
      | ~ v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_99,c_301])).

tff(c_316,plain,(
    ! [A_1] :
      ( ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_169,c_312])).

tff(c_319,plain,(
    ! [A_1] :
      ( v2_struct_0('#skF_3')
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_316])).

tff(c_320,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_319])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:51:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.27  
% 2.39/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.27  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.39/1.27  
% 2.39/1.27  %Foreground sorts:
% 2.39/1.27  
% 2.39/1.27  
% 2.39/1.27  %Background operators:
% 2.39/1.27  
% 2.39/1.27  
% 2.39/1.27  %Foreground operators:
% 2.39/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.39/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.39/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.27  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.39/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.39/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.27  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.39/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.39/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.39/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.39/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.27  
% 2.58/1.29  tff(f_100, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.58/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.58/1.29  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.58/1.29  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.58/1.29  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.58/1.29  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.58/1.29  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.58/1.29  tff(f_85, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.58/1.29  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.29  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.29  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.29  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.29  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.29  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.29  tff(c_37, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.58/1.29  tff(c_88, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.58/1.29  tff(c_95, plain, (![A_43, A_44]: (~v1_xboole_0(A_43) | ~r2_hidden(A_44, A_43))), inference(resolution, [status(thm)], [c_37, c_88])).
% 2.58/1.29  tff(c_99, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_95])).
% 2.58/1.29  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.29  tff(c_148, plain, (![B_65, A_66]: (v2_tex_2(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~v1_xboole_0(B_65) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.58/1.29  tff(c_160, plain, (![A_68, A_69]: (v2_tex_2(A_68, A_69) | ~v1_xboole_0(A_68) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69) | ~r1_tarski(A_68, u1_struct_0(A_69)))), inference(resolution, [status(thm)], [c_16, c_148])).
% 2.58/1.29  tff(c_169, plain, (![A_1, A_69]: (v2_tex_2(A_1, A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69) | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_99, c_160])).
% 2.58/1.29  tff(c_32, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.29  tff(c_200, plain, (![A_77, B_78]: (v3_tex_2('#skF_2'(A_77, B_78), A_77) | ~v2_tex_2(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v3_tdlat_3(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.29  tff(c_277, plain, (![A_85, A_86]: (v3_tex_2('#skF_2'(A_85, A_86), A_85) | ~v2_tex_2(A_86, A_85) | ~l1_pre_topc(A_85) | ~v3_tdlat_3(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85) | ~r1_tarski(A_86, u1_struct_0(A_85)))), inference(resolution, [status(thm)], [c_16, c_200])).
% 2.58/1.29  tff(c_219, plain, (![A_80, B_81]: (m1_subset_1('#skF_2'(A_80, B_81), k1_zfmisc_1(u1_struct_0(A_80))) | ~v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v3_tdlat_3(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.29  tff(c_28, plain, (![B_23]: (~v3_tex_2(B_23, '#skF_3') | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.58/1.29  tff(c_229, plain, (![B_81]: (~v3_tex_2('#skF_2'('#skF_3', B_81), '#skF_3') | ~v2_tex_2(B_81, '#skF_3') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_219, c_28])).
% 2.58/1.29  tff(c_238, plain, (![B_81]: (~v3_tex_2('#skF_2'('#skF_3', B_81), '#skF_3') | ~v2_tex_2(B_81, '#skF_3') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_229])).
% 2.58/1.29  tff(c_248, plain, (![B_82]: (~v3_tex_2('#skF_2'('#skF_3', B_82), '#skF_3') | ~v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_238])).
% 2.58/1.29  tff(c_265, plain, (![A_8]: (~v3_tex_2('#skF_2'('#skF_3', A_8), '#skF_3') | ~v2_tex_2(A_8, '#skF_3') | ~r1_tarski(A_8, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_248])).
% 2.58/1.29  tff(c_281, plain, (![A_86]: (~v2_tex_2(A_86, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_86, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_277, c_265])).
% 2.58/1.29  tff(c_291, plain, (![A_86]: (~v2_tex_2(A_86, '#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_86, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_281])).
% 2.58/1.29  tff(c_301, plain, (![A_87]: (~v2_tex_2(A_87, '#skF_3') | ~r1_tarski(A_87, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_291])).
% 2.58/1.29  tff(c_312, plain, (![A_88]: (~v2_tex_2(A_88, '#skF_3') | ~v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_99, c_301])).
% 2.58/1.29  tff(c_316, plain, (![A_1]: (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_169, c_312])).
% 2.58/1.29  tff(c_319, plain, (![A_1]: (v2_struct_0('#skF_3') | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_316])).
% 2.58/1.29  tff(c_320, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(negUnitSimplification, [status(thm)], [c_36, c_319])).
% 2.58/1.29  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.29  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_8])).
% 2.58/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.29  
% 2.58/1.29  Inference rules
% 2.58/1.29  ----------------------
% 2.58/1.29  #Ref     : 0
% 2.58/1.29  #Sup     : 54
% 2.58/1.29  #Fact    : 0
% 2.58/1.29  #Define  : 0
% 2.58/1.29  #Split   : 1
% 2.58/1.29  #Chain   : 0
% 2.58/1.29  #Close   : 0
% 2.58/1.29  
% 2.58/1.29  Ordering : KBO
% 2.58/1.29  
% 2.58/1.29  Simplification rules
% 2.58/1.29  ----------------------
% 2.58/1.29  #Subsume      : 28
% 2.58/1.29  #Demod        : 28
% 2.58/1.29  #Tautology    : 5
% 2.58/1.29  #SimpNegUnit  : 10
% 2.58/1.29  #BackRed      : 1
% 2.58/1.29  
% 2.58/1.29  #Partial instantiations: 0
% 2.58/1.29  #Strategies tried      : 1
% 2.58/1.29  
% 2.58/1.29  Timing (in seconds)
% 2.58/1.29  ----------------------
% 2.58/1.29  Preprocessing        : 0.29
% 2.58/1.29  Parsing              : 0.16
% 2.58/1.29  CNF conversion       : 0.02
% 2.58/1.29  Main loop            : 0.24
% 2.58/1.29  Inferencing          : 0.10
% 2.58/1.29  Reduction            : 0.06
% 2.58/1.29  Demodulation         : 0.04
% 2.58/1.29  BG Simplification    : 0.01
% 2.58/1.29  Subsumption          : 0.05
% 2.58/1.29  Abstraction          : 0.01
% 2.58/1.29  MUC search           : 0.00
% 2.58/1.29  Cooper               : 0.00
% 2.58/1.29  Total                : 0.56
% 2.58/1.29  Index Insertion      : 0.00
% 2.58/1.29  Index Deletion       : 0.00
% 2.58/1.29  Index Matching       : 0.00
% 2.58/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
