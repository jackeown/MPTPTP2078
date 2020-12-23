%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:33 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 109 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 265 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_mcart_1 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_32,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_98,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_3,B_4] : m1_subset_1(k6_subset_1(A_3,B_4),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_3,B_4] : m1_subset_1(k4_xboole_0(A_3,B_4),k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8])).

tff(c_201,plain,(
    ! [C_67,B_68,A_69] :
      ( ~ v1_xboole_0(C_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(C_67))
      | ~ r2_hidden(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_223,plain,(
    ! [A_71,A_72,B_73] :
      ( ~ v1_xboole_0(A_71)
      | ~ r2_hidden(A_72,k4_xboole_0(A_71,B_73)) ) ),
    inference(resolution,[status(thm)],[c_41,c_201])).

tff(c_242,plain,(
    ! [A_74,B_75] :
      ( ~ v1_xboole_0(A_74)
      | k4_xboole_0(A_74,B_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_223])).

tff(c_245,plain,(
    ! [B_75] : k4_xboole_0(k1_xboole_0,B_75) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_242])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_341,plain,(
    ! [B_104,A_105] :
      ( v2_tex_2(B_104,A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v1_xboole_0(B_104)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_352,plain,(
    ! [A_106,A_107] :
      ( v2_tex_2(A_106,A_107)
      | ~ v1_xboole_0(A_106)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ r1_tarski(A_106,u1_struct_0(A_107)) ) ),
    inference(resolution,[status(thm)],[c_14,c_341])).

tff(c_363,plain,(
    ! [A_108,A_109] :
      ( v2_tex_2(A_108,A_109)
      | ~ v1_xboole_0(A_108)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109)
      | k4_xboole_0(A_108,u1_struct_0(A_109)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_352])).

tff(c_367,plain,(
    ! [A_109] :
      ( v2_tex_2(k1_xboole_0,A_109)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_363])).

tff(c_374,plain,(
    ! [A_109] :
      ( v2_tex_2(k1_xboole_0,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_36,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_377,plain,(
    ! [A_111,B_112] :
      ( v3_tex_2('#skF_2'(A_111,B_112),A_111)
      | ~ v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v3_tdlat_3(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_384,plain,(
    ! [A_111,A_7] :
      ( v3_tex_2('#skF_2'(A_111,A_7),A_111)
      | ~ v2_tex_2(A_7,A_111)
      | ~ l1_pre_topc(A_111)
      | ~ v3_tdlat_3(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111)
      | ~ r1_tarski(A_7,u1_struct_0(A_111)) ) ),
    inference(resolution,[status(thm)],[c_14,c_377])).

tff(c_417,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1('#skF_2'(A_127,B_128),k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v3_tdlat_3(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    ! [B_40] :
      ( ~ v3_tex_2(B_40,'#skF_3')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_433,plain,(
    ! [B_128] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_128),'#skF_3')
      | ~ v2_tex_2(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_417,c_32])).

tff(c_441,plain,(
    ! [B_128] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_128),'#skF_3')
      | ~ v2_tex_2(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_433])).

tff(c_443,plain,(
    ! [B_129] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_129),'#skF_3')
      | ~ v2_tex_2(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_441])).

tff(c_462,plain,(
    ! [A_130] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',A_130),'#skF_3')
      | ~ v2_tex_2(A_130,'#skF_3')
      | ~ r1_tarski(A_130,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_443])).

tff(c_470,plain,(
    ! [A_7] :
      ( ~ v2_tex_2(A_7,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_7,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_384,c_462])).

tff(c_477,plain,(
    ! [A_7] :
      ( ~ v2_tex_2(A_7,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_7,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_470])).

tff(c_489,plain,(
    ! [A_133] :
      ( ~ v2_tex_2(A_133,'#skF_3')
      | ~ r1_tarski(A_133,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_477])).

tff(c_500,plain,(
    ! [A_134] :
      ( ~ v2_tex_2(A_134,'#skF_3')
      | k4_xboole_0(A_134,u1_struct_0('#skF_3')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_489])).

tff(c_509,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_500])).

tff(c_513,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_509])).

tff(c_516,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_513])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_mcart_1 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.54/1.36  
% 2.54/1.36  %Foreground sorts:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Background operators:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Foreground operators:
% 2.54/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.54/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.36  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.54/1.36  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.54/1.36  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.54/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.36  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.78/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.36  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.78/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.36  
% 2.78/1.38  tff(f_113, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.78/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.78/1.38  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.78/1.38  tff(f_34, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.78/1.38  tff(f_32, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.78/1.38  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.78/1.38  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.78/1.38  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.38  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.78/1.38  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.78/1.38  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.38  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.38  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.78/1.38  tff(c_18, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.38  tff(c_10, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.78/1.38  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k6_subset_1(A_3, B_4), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.38  tff(c_41, plain, (![A_3, B_4]: (m1_subset_1(k4_xboole_0(A_3, B_4), k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8])).
% 2.78/1.38  tff(c_201, plain, (![C_67, B_68, A_69]: (~v1_xboole_0(C_67) | ~m1_subset_1(B_68, k1_zfmisc_1(C_67)) | ~r2_hidden(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.38  tff(c_223, plain, (![A_71, A_72, B_73]: (~v1_xboole_0(A_71) | ~r2_hidden(A_72, k4_xboole_0(A_71, B_73)))), inference(resolution, [status(thm)], [c_41, c_201])).
% 2.78/1.38  tff(c_242, plain, (![A_74, B_75]: (~v1_xboole_0(A_74) | k4_xboole_0(A_74, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_223])).
% 2.78/1.38  tff(c_245, plain, (![B_75]: (k4_xboole_0(k1_xboole_0, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_242])).
% 2.78/1.38  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.78/1.38  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.78/1.38  tff(c_341, plain, (![B_104, A_105]: (v2_tex_2(B_104, A_105) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~v1_xboole_0(B_104) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.38  tff(c_352, plain, (![A_106, A_107]: (v2_tex_2(A_106, A_107) | ~v1_xboole_0(A_106) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107) | ~r1_tarski(A_106, u1_struct_0(A_107)))), inference(resolution, [status(thm)], [c_14, c_341])).
% 2.78/1.38  tff(c_363, plain, (![A_108, A_109]: (v2_tex_2(A_108, A_109) | ~v1_xboole_0(A_108) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109) | k4_xboole_0(A_108, u1_struct_0(A_109))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_352])).
% 2.78/1.38  tff(c_367, plain, (![A_109]: (v2_tex_2(k1_xboole_0, A_109) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(superposition, [status(thm), theory('equality')], [c_245, c_363])).
% 2.78/1.38  tff(c_374, plain, (![A_109]: (v2_tex_2(k1_xboole_0, A_109) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_367])).
% 2.78/1.38  tff(c_36, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.38  tff(c_377, plain, (![A_111, B_112]: (v3_tex_2('#skF_2'(A_111, B_112), A_111) | ~v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v3_tdlat_3(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.38  tff(c_384, plain, (![A_111, A_7]: (v3_tex_2('#skF_2'(A_111, A_7), A_111) | ~v2_tex_2(A_7, A_111) | ~l1_pre_topc(A_111) | ~v3_tdlat_3(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111) | ~r1_tarski(A_7, u1_struct_0(A_111)))), inference(resolution, [status(thm)], [c_14, c_377])).
% 2.78/1.38  tff(c_417, plain, (![A_127, B_128]: (m1_subset_1('#skF_2'(A_127, B_128), k1_zfmisc_1(u1_struct_0(A_127))) | ~v2_tex_2(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v3_tdlat_3(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.38  tff(c_32, plain, (![B_40]: (~v3_tex_2(B_40, '#skF_3') | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.38  tff(c_433, plain, (![B_128]: (~v3_tex_2('#skF_2'('#skF_3', B_128), '#skF_3') | ~v2_tex_2(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_417, c_32])).
% 2.78/1.38  tff(c_441, plain, (![B_128]: (~v3_tex_2('#skF_2'('#skF_3', B_128), '#skF_3') | ~v2_tex_2(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_433])).
% 2.78/1.38  tff(c_443, plain, (![B_129]: (~v3_tex_2('#skF_2'('#skF_3', B_129), '#skF_3') | ~v2_tex_2(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_441])).
% 2.78/1.38  tff(c_462, plain, (![A_130]: (~v3_tex_2('#skF_2'('#skF_3', A_130), '#skF_3') | ~v2_tex_2(A_130, '#skF_3') | ~r1_tarski(A_130, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_443])).
% 2.78/1.38  tff(c_470, plain, (![A_7]: (~v2_tex_2(A_7, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_7, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_384, c_462])).
% 2.78/1.38  tff(c_477, plain, (![A_7]: (~v2_tex_2(A_7, '#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_7, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_470])).
% 2.78/1.38  tff(c_489, plain, (![A_133]: (~v2_tex_2(A_133, '#skF_3') | ~r1_tarski(A_133, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_477])).
% 2.78/1.38  tff(c_500, plain, (![A_134]: (~v2_tex_2(A_134, '#skF_3') | k4_xboole_0(A_134, u1_struct_0('#skF_3'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_489])).
% 2.78/1.38  tff(c_509, plain, (~v2_tex_2(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_245, c_500])).
% 2.78/1.38  tff(c_513, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_374, c_509])).
% 2.78/1.38  tff(c_516, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_513])).
% 2.78/1.38  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_516])).
% 2.78/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.38  
% 2.78/1.38  Inference rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Ref     : 0
% 2.78/1.38  #Sup     : 101
% 2.78/1.38  #Fact    : 0
% 2.78/1.38  #Define  : 0
% 2.78/1.38  #Split   : 0
% 2.78/1.38  #Chain   : 0
% 2.78/1.38  #Close   : 0
% 2.78/1.38  
% 2.78/1.38  Ordering : KBO
% 2.78/1.38  
% 2.78/1.38  Simplification rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Subsume      : 13
% 2.78/1.38  #Demod        : 50
% 2.78/1.38  #Tautology    : 42
% 2.78/1.38  #SimpNegUnit  : 6
% 2.78/1.38  #BackRed      : 0
% 2.78/1.38  
% 2.78/1.38  #Partial instantiations: 0
% 2.78/1.38  #Strategies tried      : 1
% 2.78/1.38  
% 2.78/1.38  Timing (in seconds)
% 2.78/1.38  ----------------------
% 2.78/1.38  Preprocessing        : 0.32
% 2.78/1.38  Parsing              : 0.17
% 2.78/1.38  CNF conversion       : 0.02
% 2.78/1.38  Main loop            : 0.28
% 2.78/1.38  Inferencing          : 0.12
% 2.78/1.38  Reduction            : 0.08
% 2.78/1.38  Demodulation         : 0.06
% 2.78/1.38  BG Simplification    : 0.02
% 2.78/1.39  Subsumption          : 0.05
% 2.78/1.39  Abstraction          : 0.02
% 2.78/1.39  MUC search           : 0.00
% 2.78/1.39  Cooper               : 0.00
% 2.78/1.39  Total                : 0.64
% 2.78/1.39  Index Insertion      : 0.00
% 2.78/1.39  Index Deletion       : 0.00
% 2.78/1.39  Index Matching       : 0.00
% 2.78/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
