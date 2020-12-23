%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:33 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 269 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

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

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [B_47,A_48,A_49] :
      ( ~ v1_xboole_0(B_47)
      | ~ r2_hidden(A_48,A_49)
      | ~ r1_tarski(A_49,B_47) ) ),
    inference(resolution,[status(thm)],[c_14,c_151])).

tff(c_159,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | ~ r1_tarski(A_51,B_50)
      | k1_xboole_0 = A_51 ) ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_186,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | k4_xboole_0(A_54,B_55) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_189,plain,(
    ! [B_55] : k4_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_186])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_180,plain,(
    ! [B_52,A_53] :
      ( v2_tex_2(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ v1_xboole_0(B_52)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_237,plain,(
    ! [A_62,A_63] :
      ( v2_tex_2(A_62,A_63)
      | ~ v1_xboole_0(A_62)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63)
      | ~ r1_tarski(A_62,u1_struct_0(A_63)) ) ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_248,plain,(
    ! [A_64,A_65] :
      ( v2_tex_2(A_64,A_65)
      | ~ v1_xboole_0(A_64)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | k4_xboole_0(A_64,u1_struct_0(A_65)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_237])).

tff(c_252,plain,(
    ! [A_65] :
      ( v2_tex_2(k1_xboole_0,A_65)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_248])).

tff(c_259,plain,(
    ! [A_65] :
      ( v2_tex_2(k1_xboole_0,A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_252])).

tff(c_30,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_262,plain,(
    ! [A_67,B_68] :
      ( v3_tex_2('#skF_2'(A_67,B_68),A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_266,plain,(
    ! [A_67,A_7] :
      ( v3_tex_2('#skF_2'(A_67,A_7),A_67)
      | ~ v2_tex_2(A_7,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ r1_tarski(A_7,u1_struct_0(A_67)) ) ),
    inference(resolution,[status(thm)],[c_14,c_262])).

tff(c_269,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1('#skF_2'(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v3_tdlat_3(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    ! [B_22] :
      ( ~ v3_tex_2(B_22,'#skF_3')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_285,plain,(
    ! [B_74] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_74),'#skF_3')
      | ~ v2_tex_2(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_269,c_26])).

tff(c_293,plain,(
    ! [B_74] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_74),'#skF_3')
      | ~ v2_tex_2(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_285])).

tff(c_295,plain,(
    ! [B_75] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_75),'#skF_3')
      | ~ v2_tex_2(B_75,'#skF_3')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_293])).

tff(c_309,plain,(
    ! [A_76] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',A_76),'#skF_3')
      | ~ v2_tex_2(A_76,'#skF_3')
      | ~ r1_tarski(A_76,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_295])).

tff(c_313,plain,(
    ! [A_7] :
      ( ~ v2_tex_2(A_7,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_7,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_266,c_309])).

tff(c_316,plain,(
    ! [A_7] :
      ( ~ v2_tex_2(A_7,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_7,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_313])).

tff(c_318,plain,(
    ! [A_77] :
      ( ~ v2_tex_2(A_77,'#skF_3')
      | ~ r1_tarski(A_77,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_316])).

tff(c_348,plain,(
    ! [A_82] :
      ( ~ v2_tex_2(A_82,'#skF_3')
      | k4_xboole_0(A_82,u1_struct_0('#skF_3')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_318])).

tff(c_357,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_348])).

tff(c_361,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_259,c_357])).

tff(c_364,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_361])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.77  
% 2.72/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.77  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.72/1.77  
% 2.72/1.77  %Foreground sorts:
% 2.72/1.77  
% 2.72/1.77  
% 2.72/1.77  %Background operators:
% 2.72/1.77  
% 2.72/1.77  
% 2.72/1.77  %Foreground operators:
% 2.72/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.72/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.72/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.72/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.77  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.72/1.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.72/1.77  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.77  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.72/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.72/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.72/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.72/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.72/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.77  
% 3.00/1.80  tff(f_103, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 3.00/1.80  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.00/1.80  tff(f_40, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.00/1.80  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.00/1.80  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.00/1.80  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.00/1.80  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.00/1.80  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 3.00/1.80  tff(f_88, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 3.00/1.80  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.80  tff(c_32, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.80  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.80  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.00/1.80  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.00/1.80  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.80  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.80  tff(c_151, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.80  tff(c_155, plain, (![B_47, A_48, A_49]: (~v1_xboole_0(B_47) | ~r2_hidden(A_48, A_49) | ~r1_tarski(A_49, B_47))), inference(resolution, [status(thm)], [c_14, c_151])).
% 3.00/1.80  tff(c_159, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | ~r1_tarski(A_51, B_50) | k1_xboole_0=A_51)), inference(resolution, [status(thm)], [c_4, c_155])).
% 3.00/1.80  tff(c_186, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | k4_xboole_0(A_54, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_159])).
% 3.00/1.80  tff(c_189, plain, (![B_55]: (k4_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_186])).
% 3.00/1.80  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.80  tff(c_180, plain, (![B_52, A_53]: (v2_tex_2(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~v1_xboole_0(B_52) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.80  tff(c_237, plain, (![A_62, A_63]: (v2_tex_2(A_62, A_63) | ~v1_xboole_0(A_62) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63) | ~r1_tarski(A_62, u1_struct_0(A_63)))), inference(resolution, [status(thm)], [c_14, c_180])).
% 3.00/1.80  tff(c_248, plain, (![A_64, A_65]: (v2_tex_2(A_64, A_65) | ~v1_xboole_0(A_64) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | k4_xboole_0(A_64, u1_struct_0(A_65))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_237])).
% 3.00/1.80  tff(c_252, plain, (![A_65]: (v2_tex_2(k1_xboole_0, A_65) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(superposition, [status(thm), theory('equality')], [c_189, c_248])).
% 3.00/1.80  tff(c_259, plain, (![A_65]: (v2_tex_2(k1_xboole_0, A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_252])).
% 3.00/1.80  tff(c_30, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.80  tff(c_262, plain, (![A_67, B_68]: (v3_tex_2('#skF_2'(A_67, B_68), A_67) | ~v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v3_tdlat_3(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.00/1.80  tff(c_266, plain, (![A_67, A_7]: (v3_tex_2('#skF_2'(A_67, A_7), A_67) | ~v2_tex_2(A_7, A_67) | ~l1_pre_topc(A_67) | ~v3_tdlat_3(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~r1_tarski(A_7, u1_struct_0(A_67)))), inference(resolution, [status(thm)], [c_14, c_262])).
% 3.00/1.80  tff(c_269, plain, (![A_73, B_74]: (m1_subset_1('#skF_2'(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v3_tdlat_3(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.00/1.80  tff(c_26, plain, (![B_22]: (~v3_tex_2(B_22, '#skF_3') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.80  tff(c_285, plain, (![B_74]: (~v3_tex_2('#skF_2'('#skF_3', B_74), '#skF_3') | ~v2_tex_2(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_269, c_26])).
% 3.00/1.80  tff(c_293, plain, (![B_74]: (~v3_tex_2('#skF_2'('#skF_3', B_74), '#skF_3') | ~v2_tex_2(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_285])).
% 3.00/1.80  tff(c_295, plain, (![B_75]: (~v3_tex_2('#skF_2'('#skF_3', B_75), '#skF_3') | ~v2_tex_2(B_75, '#skF_3') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_293])).
% 3.00/1.80  tff(c_309, plain, (![A_76]: (~v3_tex_2('#skF_2'('#skF_3', A_76), '#skF_3') | ~v2_tex_2(A_76, '#skF_3') | ~r1_tarski(A_76, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_295])).
% 3.00/1.80  tff(c_313, plain, (![A_7]: (~v2_tex_2(A_7, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_7, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_266, c_309])).
% 3.00/1.80  tff(c_316, plain, (![A_7]: (~v2_tex_2(A_7, '#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_7, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_313])).
% 3.00/1.80  tff(c_318, plain, (![A_77]: (~v2_tex_2(A_77, '#skF_3') | ~r1_tarski(A_77, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_34, c_316])).
% 3.00/1.80  tff(c_348, plain, (![A_82]: (~v2_tex_2(A_82, '#skF_3') | k4_xboole_0(A_82, u1_struct_0('#skF_3'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_318])).
% 3.00/1.80  tff(c_357, plain, (~v2_tex_2(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_189, c_348])).
% 3.00/1.80  tff(c_361, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_259, c_357])).
% 3.00/1.80  tff(c_364, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_361])).
% 3.00/1.80  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_364])).
% 3.00/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.80  
% 3.00/1.80  Inference rules
% 3.00/1.80  ----------------------
% 3.00/1.80  #Ref     : 0
% 3.00/1.80  #Sup     : 69
% 3.00/1.80  #Fact    : 0
% 3.00/1.80  #Define  : 0
% 3.00/1.80  #Split   : 0
% 3.00/1.80  #Chain   : 0
% 3.00/1.80  #Close   : 0
% 3.00/1.80  
% 3.00/1.80  Ordering : KBO
% 3.00/1.80  
% 3.00/1.80  Simplification rules
% 3.00/1.80  ----------------------
% 3.00/1.80  #Subsume      : 4
% 3.00/1.80  #Demod        : 33
% 3.00/1.80  #Tautology    : 31
% 3.00/1.80  #SimpNegUnit  : 5
% 3.00/1.80  #BackRed      : 0
% 3.00/1.80  
% 3.00/1.80  #Partial instantiations: 0
% 3.00/1.80  #Strategies tried      : 1
% 3.00/1.80  
% 3.00/1.80  Timing (in seconds)
% 3.00/1.80  ----------------------
% 3.00/1.80  Preprocessing        : 0.45
% 3.00/1.80  Parsing              : 0.24
% 3.00/1.81  CNF conversion       : 0.03
% 3.00/1.81  Main loop            : 0.45
% 3.00/1.81  Inferencing          : 0.18
% 3.00/1.81  Reduction            : 0.12
% 3.00/1.81  Demodulation         : 0.08
% 3.00/1.81  BG Simplification    : 0.02
% 3.00/1.81  Subsumption          : 0.10
% 3.00/1.81  Abstraction          : 0.02
% 3.00/1.81  MUC search           : 0.00
% 3.00/1.81  Cooper               : 0.00
% 3.00/1.81  Total                : 0.95
% 3.00/1.81  Index Insertion      : 0.00
% 3.00/1.81  Index Deletion       : 0.00
% 3.00/1.81  Index Matching       : 0.00
% 3.00/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
