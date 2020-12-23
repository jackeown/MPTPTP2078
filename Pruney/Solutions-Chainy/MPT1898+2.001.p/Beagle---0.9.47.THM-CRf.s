%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:30 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   61 (  95 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 247 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_88,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_tarski(A_41),k1_zfmisc_1(B_42))
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_41,B_42] :
      ( v1_xboole_0(k1_tarski(A_41))
      | ~ v1_xboole_0(B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_74,c_14])).

tff(c_90,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_77])).

tff(c_94,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,(
    ! [B_60,A_61] :
      ( v2_tex_2(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ v1_xboole_0(B_60)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_166,plain,(
    ! [A_66,A_67] :
      ( v2_tex_2(A_66,A_67)
      | ~ v1_xboole_0(A_66)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ r1_tarski(A_66,u1_struct_0(A_67)) ) ),
    inference(resolution,[status(thm)],[c_18,c_145])).

tff(c_180,plain,(
    ! [A_1,A_67] :
      ( v2_tex_2(A_1,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_94,c_166])).

tff(c_32,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_183,plain,(
    ! [A_70,B_71] :
      ( v3_tex_2('#skF_2'(A_70,B_71),A_70)
      | ~ v2_tex_2(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v3_tdlat_3(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_331,plain,(
    ! [A_101,A_102] :
      ( v3_tex_2('#skF_2'(A_101,A_102),A_101)
      | ~ v2_tex_2(A_102,A_101)
      | ~ l1_pre_topc(A_101)
      | ~ v3_tdlat_3(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101)
      | ~ r1_tarski(A_102,u1_struct_0(A_101)) ) ),
    inference(resolution,[status(thm)],[c_18,c_183])).

tff(c_273,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1('#skF_2'(A_95,B_96),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v3_tdlat_3(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [B_24] :
      ( ~ v3_tex_2(B_24,'#skF_3')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_284,plain,(
    ! [B_96] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_96),'#skF_3')
      | ~ v2_tex_2(B_96,'#skF_3')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_273,c_28])).

tff(c_293,plain,(
    ! [B_96] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_96),'#skF_3')
      | ~ v2_tex_2(B_96,'#skF_3')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_284])).

tff(c_296,plain,(
    ! [B_97] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_97),'#skF_3')
      | ~ v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_293])).

tff(c_314,plain,(
    ! [A_12] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',A_12),'#skF_3')
      | ~ v2_tex_2(A_12,'#skF_3')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_338,plain,(
    ! [A_102] :
      ( ~ v2_tex_2(A_102,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_102,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_331,c_314])).

tff(c_349,plain,(
    ! [A_102] :
      ( ~ v2_tex_2(A_102,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_102,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_338])).

tff(c_380,plain,(
    ! [A_105] :
      ( ~ v2_tex_2(A_105,'#skF_3')
      | ~ r1_tarski(A_105,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_349])).

tff(c_411,plain,(
    ! [A_107] :
      ( ~ v2_tex_2(A_107,'#skF_3')
      | ~ v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_94,c_380])).

tff(c_415,plain,(
    ! [A_1] :
      ( ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_180,c_411])).

tff(c_418,plain,(
    ! [A_1] :
      ( v2_struct_0('#skF_3')
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_415])).

tff(c_419,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_418])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.37  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.45/1.37  
% 2.45/1.37  %Foreground sorts:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Background operators:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Foreground operators:
% 2.45/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.37  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.45/1.37  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.45/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.37  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.45/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.45/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.37  
% 2.45/1.39  tff(f_103, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.45/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.39  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.45/1.39  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.45/1.39  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.45/1.39  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.45/1.39  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.45/1.39  tff(f_88, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.45/1.39  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.45/1.39  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.45/1.39  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.45/1.39  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.45/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.39  tff(c_10, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.45/1.39  tff(c_74, plain, (![A_41, B_42]: (m1_subset_1(k1_tarski(A_41), k1_zfmisc_1(B_42)) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.45/1.39  tff(c_14, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.45/1.39  tff(c_77, plain, (![A_41, B_42]: (v1_xboole_0(k1_tarski(A_41)) | ~v1_xboole_0(B_42) | ~r2_hidden(A_41, B_42))), inference(resolution, [status(thm)], [c_74, c_14])).
% 2.45/1.39  tff(c_90, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | ~r2_hidden(A_44, B_43))), inference(negUnitSimplification, [status(thm)], [c_10, c_77])).
% 2.45/1.39  tff(c_94, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.45/1.39  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.39  tff(c_145, plain, (![B_60, A_61]: (v2_tex_2(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~v1_xboole_0(B_60) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.39  tff(c_166, plain, (![A_66, A_67]: (v2_tex_2(A_66, A_67) | ~v1_xboole_0(A_66) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~r1_tarski(A_66, u1_struct_0(A_67)))), inference(resolution, [status(thm)], [c_18, c_145])).
% 2.45/1.39  tff(c_180, plain, (![A_1, A_67]: (v2_tex_2(A_1, A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_94, c_166])).
% 2.45/1.39  tff(c_32, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.45/1.39  tff(c_183, plain, (![A_70, B_71]: (v3_tex_2('#skF_2'(A_70, B_71), A_70) | ~v2_tex_2(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v3_tdlat_3(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.45/1.39  tff(c_331, plain, (![A_101, A_102]: (v3_tex_2('#skF_2'(A_101, A_102), A_101) | ~v2_tex_2(A_102, A_101) | ~l1_pre_topc(A_101) | ~v3_tdlat_3(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101) | ~r1_tarski(A_102, u1_struct_0(A_101)))), inference(resolution, [status(thm)], [c_18, c_183])).
% 2.45/1.39  tff(c_273, plain, (![A_95, B_96]: (m1_subset_1('#skF_2'(A_95, B_96), k1_zfmisc_1(u1_struct_0(A_95))) | ~v2_tex_2(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v3_tdlat_3(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.45/1.39  tff(c_28, plain, (![B_24]: (~v3_tex_2(B_24, '#skF_3') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.45/1.39  tff(c_284, plain, (![B_96]: (~v3_tex_2('#skF_2'('#skF_3', B_96), '#skF_3') | ~v2_tex_2(B_96, '#skF_3') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_273, c_28])).
% 2.45/1.39  tff(c_293, plain, (![B_96]: (~v3_tex_2('#skF_2'('#skF_3', B_96), '#skF_3') | ~v2_tex_2(B_96, '#skF_3') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_284])).
% 2.45/1.39  tff(c_296, plain, (![B_97]: (~v3_tex_2('#skF_2'('#skF_3', B_97), '#skF_3') | ~v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_293])).
% 2.45/1.39  tff(c_314, plain, (![A_12]: (~v3_tex_2('#skF_2'('#skF_3', A_12), '#skF_3') | ~v2_tex_2(A_12, '#skF_3') | ~r1_tarski(A_12, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_296])).
% 2.45/1.39  tff(c_338, plain, (![A_102]: (~v2_tex_2(A_102, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_102, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_331, c_314])).
% 2.45/1.39  tff(c_349, plain, (![A_102]: (~v2_tex_2(A_102, '#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_102, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_338])).
% 2.45/1.39  tff(c_380, plain, (![A_105]: (~v2_tex_2(A_105, '#skF_3') | ~r1_tarski(A_105, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_349])).
% 2.45/1.39  tff(c_411, plain, (![A_107]: (~v2_tex_2(A_107, '#skF_3') | ~v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_94, c_380])).
% 2.45/1.39  tff(c_415, plain, (![A_1]: (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_180, c_411])).
% 2.45/1.39  tff(c_418, plain, (![A_1]: (v2_struct_0('#skF_3') | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_415])).
% 2.45/1.39  tff(c_419, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(negUnitSimplification, [status(thm)], [c_36, c_418])).
% 2.45/1.39  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.39  tff(c_423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_8])).
% 2.45/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.39  
% 2.45/1.39  Inference rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Ref     : 0
% 2.45/1.39  #Sup     : 75
% 2.45/1.39  #Fact    : 0
% 2.45/1.39  #Define  : 0
% 2.45/1.39  #Split   : 0
% 2.45/1.39  #Chain   : 0
% 2.45/1.39  #Close   : 0
% 2.45/1.39  
% 2.45/1.39  Ordering : KBO
% 2.45/1.39  
% 2.45/1.39  Simplification rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Subsume      : 32
% 2.45/1.39  #Demod        : 30
% 2.45/1.39  #Tautology    : 4
% 2.45/1.39  #SimpNegUnit  : 16
% 2.45/1.39  #BackRed      : 1
% 2.45/1.39  
% 2.45/1.39  #Partial instantiations: 0
% 2.45/1.39  #Strategies tried      : 1
% 2.45/1.39  
% 2.45/1.39  Timing (in seconds)
% 2.45/1.39  ----------------------
% 2.45/1.39  Preprocessing        : 0.31
% 2.45/1.39  Parsing              : 0.18
% 2.45/1.39  CNF conversion       : 0.02
% 2.45/1.39  Main loop            : 0.29
% 2.45/1.39  Inferencing          : 0.12
% 2.45/1.39  Reduction            : 0.07
% 2.45/1.40  Demodulation         : 0.04
% 2.45/1.40  BG Simplification    : 0.01
% 2.45/1.40  Subsumption          : 0.07
% 2.76/1.40  Abstraction          : 0.01
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.63
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
