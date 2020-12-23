%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:30 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 166 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 503 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_211,plain,(
    ! [B_70,A_71] :
      ( l1_pre_topc(B_70)
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_214,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_211])).

tff(c_223,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_214])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_217,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_211])).

tff(c_226,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_217])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_56,plain,(
    ! [B_32,A_33] :
      ( l1_pre_topc(B_32)
      | ~ m1_pre_topc(B_32,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59])).

tff(c_28,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_47,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_82,plain,(
    ! [B_36,A_37] :
      ( r1_tsep_1(B_36,A_37)
      | ~ r1_tsep_1(A_37,B_36)
      | ~ l1_struct_0(B_36)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_82])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_89,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_89])).

tff(c_95,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_71,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_62])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_94,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_100,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_96])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_100])).

tff(c_106,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_105,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_113,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(u1_struct_0(B_44),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_pre_topc(B_44,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(u1_struct_0(B_44),u1_struct_0(A_45))
      | ~ m1_pre_topc(B_44,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_113,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(u1_struct_0(A_50),u1_struct_0(B_51))
      | ~ r1_tsep_1(A_50,B_51)
      | ~ l1_struct_0(B_51)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(C_5,A_3)
      | v1_xboole_0(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ r1_tarski(C_54,u1_struct_0(B_55))
      | ~ r1_tarski(C_54,u1_struct_0(A_56))
      | v1_xboole_0(C_54)
      | ~ r1_tsep_1(A_56,B_55)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_123,c_8])).

tff(c_169,plain,(
    ! [B_59,A_60] :
      ( ~ r1_tarski(u1_struct_0(B_59),u1_struct_0(A_60))
      | v1_xboole_0(u1_struct_0(B_59))
      | ~ r1_tsep_1(A_60,B_59)
      | ~ l1_struct_0(B_59)
      | ~ l1_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_188,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(u1_struct_0(B_65))
      | ~ r1_tsep_1(A_66,B_65)
      | ~ l1_struct_0(B_65)
      | ~ l1_struct_0(A_66)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_117,c_169])).

tff(c_190,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_188])).

tff(c_195,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_30,c_106,c_95,c_190])).

tff(c_18,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_195,c_18])).

tff(c_204,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_201])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_204])).

tff(c_208,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_207,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_243,plain,(
    ! [B_77,A_78] :
      ( r1_tsep_1(B_77,A_78)
      | ~ r1_tsep_1(A_78,B_77)
      | ~ l1_struct_0(B_77)
      | ~ l1_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_245,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_207,c_243])).

tff(c_248,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_245])).

tff(c_249,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_252,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_249])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_252])).

tff(c_257,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_261,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_257])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.29  
% 2.50/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.29  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.29  
% 2.50/1.29  %Foreground sorts:
% 2.50/1.29  
% 2.50/1.29  
% 2.50/1.29  %Background operators:
% 2.50/1.29  
% 2.50/1.29  
% 2.50/1.29  %Foreground operators:
% 2.50/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.50/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.50/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.29  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.50/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.29  
% 2.50/1.31  tff(f_116, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.50/1.31  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.50/1.31  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.50/1.31  tff(f_81, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.50/1.31  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.50/1.31  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.50/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.31  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.50/1.31  tff(f_41, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.50/1.31  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.50/1.31  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.50/1.31  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.50/1.31  tff(c_211, plain, (![B_70, A_71]: (l1_pre_topc(B_70) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.50/1.31  tff(c_214, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_211])).
% 2.50/1.31  tff(c_223, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_214])).
% 2.50/1.31  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.50/1.31  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.50/1.31  tff(c_217, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_211])).
% 2.50/1.31  tff(c_226, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_217])).
% 2.50/1.31  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.50/1.31  tff(c_56, plain, (![B_32, A_33]: (l1_pre_topc(B_32) | ~m1_pre_topc(B_32, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.50/1.31  tff(c_59, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.50/1.31  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59])).
% 2.50/1.31  tff(c_28, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.50/1.31  tff(c_47, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.50/1.31  tff(c_82, plain, (![B_36, A_37]: (r1_tsep_1(B_36, A_37) | ~r1_tsep_1(A_37, B_36) | ~l1_struct_0(B_36) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.50/1.31  tff(c_85, plain, (r1_tsep_1('#skF_3', '#skF_2') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_47, c_82])).
% 2.50/1.31  tff(c_86, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_85])).
% 2.50/1.31  tff(c_89, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_86])).
% 2.50/1.31  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_89])).
% 2.50/1.31  tff(c_95, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_85])).
% 2.50/1.31  tff(c_62, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_56])).
% 2.50/1.31  tff(c_71, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_62])).
% 2.50/1.31  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.50/1.31  tff(c_94, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_85])).
% 2.50/1.31  tff(c_96, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 2.50/1.31  tff(c_100, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_96])).
% 2.50/1.31  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_100])).
% 2.50/1.31  tff(c_106, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 2.50/1.31  tff(c_105, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_94])).
% 2.50/1.31  tff(c_113, plain, (![B_44, A_45]: (m1_subset_1(u1_struct_0(B_44), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_pre_topc(B_44, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.50/1.31  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.31  tff(c_117, plain, (![B_44, A_45]: (r1_tarski(u1_struct_0(B_44), u1_struct_0(A_45)) | ~m1_pre_topc(B_44, A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_113, c_10])).
% 2.50/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.31  tff(c_123, plain, (![A_50, B_51]: (r1_xboole_0(u1_struct_0(A_50), u1_struct_0(B_51)) | ~r1_tsep_1(A_50, B_51) | ~l1_struct_0(B_51) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.50/1.31  tff(c_8, plain, (![A_3, B_4, C_5]: (~r1_xboole_0(A_3, B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(C_5, A_3) | v1_xboole_0(C_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.31  tff(c_142, plain, (![C_54, B_55, A_56]: (~r1_tarski(C_54, u1_struct_0(B_55)) | ~r1_tarski(C_54, u1_struct_0(A_56)) | v1_xboole_0(C_54) | ~r1_tsep_1(A_56, B_55) | ~l1_struct_0(B_55) | ~l1_struct_0(A_56))), inference(resolution, [status(thm)], [c_123, c_8])).
% 2.50/1.31  tff(c_169, plain, (![B_59, A_60]: (~r1_tarski(u1_struct_0(B_59), u1_struct_0(A_60)) | v1_xboole_0(u1_struct_0(B_59)) | ~r1_tsep_1(A_60, B_59) | ~l1_struct_0(B_59) | ~l1_struct_0(A_60))), inference(resolution, [status(thm)], [c_6, c_142])).
% 2.50/1.31  tff(c_188, plain, (![B_65, A_66]: (v1_xboole_0(u1_struct_0(B_65)) | ~r1_tsep_1(A_66, B_65) | ~l1_struct_0(B_65) | ~l1_struct_0(A_66) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_117, c_169])).
% 2.50/1.31  tff(c_190, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_105, c_188])).
% 2.50/1.31  tff(c_195, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_30, c_106, c_95, c_190])).
% 2.50/1.31  tff(c_18, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.50/1.31  tff(c_201, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_195, c_18])).
% 2.50/1.31  tff(c_204, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_201])).
% 2.50/1.31  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_204])).
% 2.50/1.31  tff(c_208, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.50/1.31  tff(c_207, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.50/1.31  tff(c_243, plain, (![B_77, A_78]: (r1_tsep_1(B_77, A_78) | ~r1_tsep_1(A_78, B_77) | ~l1_struct_0(B_77) | ~l1_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.50/1.31  tff(c_245, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_207, c_243])).
% 2.50/1.31  tff(c_248, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_208, c_245])).
% 2.50/1.31  tff(c_249, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_248])).
% 2.50/1.31  tff(c_252, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_249])).
% 2.50/1.31  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_252])).
% 2.50/1.31  tff(c_257, plain, (~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_248])).
% 2.50/1.31  tff(c_261, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_257])).
% 2.50/1.31  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_261])).
% 2.50/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.31  
% 2.50/1.31  Inference rules
% 2.50/1.31  ----------------------
% 2.50/1.31  #Ref     : 0
% 2.50/1.31  #Sup     : 35
% 2.50/1.31  #Fact    : 0
% 2.50/1.31  #Define  : 0
% 2.50/1.31  #Split   : 7
% 2.50/1.31  #Chain   : 0
% 2.50/1.31  #Close   : 0
% 2.50/1.31  
% 2.50/1.31  Ordering : KBO
% 2.50/1.31  
% 2.50/1.31  Simplification rules
% 2.50/1.31  ----------------------
% 2.50/1.31  #Subsume      : 1
% 2.50/1.31  #Demod        : 32
% 2.50/1.31  #Tautology    : 10
% 2.50/1.31  #SimpNegUnit  : 2
% 2.50/1.31  #BackRed      : 0
% 2.50/1.31  
% 2.50/1.31  #Partial instantiations: 0
% 2.50/1.31  #Strategies tried      : 1
% 2.50/1.31  
% 2.50/1.31  Timing (in seconds)
% 2.50/1.31  ----------------------
% 2.50/1.32  Preprocessing        : 0.31
% 2.50/1.32  Parsing              : 0.17
% 2.50/1.32  CNF conversion       : 0.02
% 2.50/1.32  Main loop            : 0.23
% 2.50/1.32  Inferencing          : 0.09
% 2.50/1.32  Reduction            : 0.06
% 2.50/1.32  Demodulation         : 0.04
% 2.50/1.32  BG Simplification    : 0.01
% 2.50/1.32  Subsumption          : 0.04
% 2.50/1.32  Abstraction          : 0.01
% 2.50/1.32  MUC search           : 0.00
% 2.50/1.32  Cooper               : 0.00
% 2.50/1.32  Total                : 0.58
% 2.50/1.32  Index Insertion      : 0.00
% 2.50/1.32  Index Deletion       : 0.00
% 2.50/1.32  Index Matching       : 0.00
% 2.50/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
