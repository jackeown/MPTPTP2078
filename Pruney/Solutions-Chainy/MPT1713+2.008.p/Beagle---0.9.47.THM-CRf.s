%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:30 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 169 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 506 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_115,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_283,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_286,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_283])).

tff(c_295,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_286])).

tff(c_16,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_292,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_283])).

tff(c_299,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_292])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    ! [B_32,A_33] :
      ( l1_pre_topc(B_32)
      | ~ m1_pre_topc(B_32,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_61])).

tff(c_30,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_84,plain,(
    ! [B_36,A_37] :
      ( r1_tsep_1(B_36,A_37)
      | ~ r1_tsep_1(A_37,B_36)
      | ~ l1_struct_0(B_36)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_88,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_91,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_88])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_91])).

tff(c_97,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_96,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_103,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_106])).

tff(c_112,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_111,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_98,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_102,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0(A_39))
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(u1_struct_0(A_45),u1_struct_0(B_46))
      | ~ r1_tsep_1(A_45,B_46)
      | ~ l1_struct_0(B_46)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( k1_xboole_0 = A_3
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [A_51,B_52,A_53] :
      ( k1_xboole_0 = A_51
      | ~ r1_tarski(A_51,u1_struct_0(B_52))
      | ~ r1_tarski(A_51,u1_struct_0(A_53))
      | ~ r1_tsep_1(A_53,B_52)
      | ~ l1_struct_0(B_52)
      | ~ l1_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_123,c_10])).

tff(c_170,plain,(
    ! [B_56,A_57] :
      ( u1_struct_0(B_56) = k1_xboole_0
      | ~ r1_tarski(u1_struct_0(B_56),u1_struct_0(A_57))
      | ~ r1_tsep_1(A_57,B_56)
      | ~ l1_struct_0(B_56)
      | ~ l1_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_189,plain,(
    ! [B_62,A_63] :
      ( u1_struct_0(B_62) = k1_xboole_0
      | ~ r1_tsep_1(A_63,B_62)
      | ~ l1_struct_0(B_62)
      | ~ l1_struct_0(A_63)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_102,c_170])).

tff(c_192,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_189])).

tff(c_198,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_32,c_112,c_97,c_192])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_247,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_20])).

tff(c_275,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_2,c_247])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_275])).

tff(c_279,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_278,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_315,plain,(
    ! [B_75,A_76] :
      ( r1_tsep_1(B_75,A_76)
      | ~ r1_tsep_1(A_76,B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_317,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_315])).

tff(c_320,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_317])).

tff(c_321,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_324,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_321])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_324])).

tff(c_329,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_333,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_329])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.29  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.29  
% 2.24/1.29  %Foreground sorts:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Background operators:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Foreground operators:
% 2.24/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.24/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.29  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.24/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.29  
% 2.24/1.31  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.24/1.31  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.24/1.31  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.24/1.31  tff(f_80, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.24/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.31  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.24/1.31  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.24/1.31  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.24/1.31  tff(f_72, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.24/1.31  tff(f_40, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.24/1.31  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.24/1.31  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.24/1.31  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.24/1.31  tff(c_283, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.31  tff(c_286, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_283])).
% 2.24/1.31  tff(c_295, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_286])).
% 2.24/1.31  tff(c_16, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.31  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.24/1.31  tff(c_292, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_283])).
% 2.24/1.31  tff(c_299, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_292])).
% 2.24/1.31  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.24/1.31  tff(c_58, plain, (![B_32, A_33]: (l1_pre_topc(B_32) | ~m1_pre_topc(B_32, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.31  tff(c_61, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.24/1.31  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_61])).
% 2.24/1.31  tff(c_30, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.24/1.31  tff(c_48, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.24/1.31  tff(c_84, plain, (![B_36, A_37]: (r1_tsep_1(B_36, A_37) | ~r1_tsep_1(A_37, B_36) | ~l1_struct_0(B_36) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.31  tff(c_87, plain, (r1_tsep_1('#skF_3', '#skF_2') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_84])).
% 2.24/1.31  tff(c_88, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_87])).
% 2.24/1.31  tff(c_91, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_88])).
% 2.24/1.31  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_91])).
% 2.24/1.31  tff(c_97, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_87])).
% 2.24/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.31  tff(c_67, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.24/1.31  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67])).
% 2.24/1.31  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.24/1.31  tff(c_96, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_87])).
% 2.24/1.31  tff(c_103, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_96])).
% 2.24/1.31  tff(c_106, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_103])).
% 2.24/1.31  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_106])).
% 2.24/1.31  tff(c_112, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_96])).
% 2.24/1.31  tff(c_111, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_96])).
% 2.24/1.31  tff(c_98, plain, (![B_38, A_39]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.24/1.31  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.24/1.31  tff(c_102, plain, (![B_38, A_39]: (r1_tarski(u1_struct_0(B_38), u1_struct_0(A_39)) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_98, c_12])).
% 2.24/1.31  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.31  tff(c_123, plain, (![A_45, B_46]: (r1_xboole_0(u1_struct_0(A_45), u1_struct_0(B_46)) | ~r1_tsep_1(A_45, B_46) | ~l1_struct_0(B_46) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.24/1.31  tff(c_10, plain, (![A_3, B_4, C_5]: (k1_xboole_0=A_3 | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.31  tff(c_143, plain, (![A_51, B_52, A_53]: (k1_xboole_0=A_51 | ~r1_tarski(A_51, u1_struct_0(B_52)) | ~r1_tarski(A_51, u1_struct_0(A_53)) | ~r1_tsep_1(A_53, B_52) | ~l1_struct_0(B_52) | ~l1_struct_0(A_53))), inference(resolution, [status(thm)], [c_123, c_10])).
% 2.24/1.31  tff(c_170, plain, (![B_56, A_57]: (u1_struct_0(B_56)=k1_xboole_0 | ~r1_tarski(u1_struct_0(B_56), u1_struct_0(A_57)) | ~r1_tsep_1(A_57, B_56) | ~l1_struct_0(B_56) | ~l1_struct_0(A_57))), inference(resolution, [status(thm)], [c_8, c_143])).
% 2.24/1.31  tff(c_189, plain, (![B_62, A_63]: (u1_struct_0(B_62)=k1_xboole_0 | ~r1_tsep_1(A_63, B_62) | ~l1_struct_0(B_62) | ~l1_struct_0(A_63) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_102, c_170])).
% 2.24/1.31  tff(c_192, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_111, c_189])).
% 2.24/1.31  tff(c_198, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_32, c_112, c_97, c_192])).
% 2.24/1.31  tff(c_20, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.31  tff(c_247, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_198, c_20])).
% 2.24/1.31  tff(c_275, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_2, c_247])).
% 2.24/1.31  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_275])).
% 2.24/1.31  tff(c_279, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.24/1.31  tff(c_278, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.24/1.31  tff(c_315, plain, (![B_75, A_76]: (r1_tsep_1(B_75, A_76) | ~r1_tsep_1(A_76, B_75) | ~l1_struct_0(B_75) | ~l1_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.31  tff(c_317, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_278, c_315])).
% 2.24/1.31  tff(c_320, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_279, c_317])).
% 2.24/1.31  tff(c_321, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_320])).
% 2.24/1.31  tff(c_324, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_321])).
% 2.24/1.31  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_324])).
% 2.24/1.31  tff(c_329, plain, (~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_320])).
% 2.24/1.31  tff(c_333, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_329])).
% 2.24/1.31  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_333])).
% 2.24/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  Inference rules
% 2.24/1.31  ----------------------
% 2.24/1.31  #Ref     : 0
% 2.24/1.31  #Sup     : 52
% 2.24/1.31  #Fact    : 0
% 2.24/1.31  #Define  : 0
% 2.24/1.31  #Split   : 7
% 2.24/1.31  #Chain   : 0
% 2.24/1.31  #Close   : 0
% 2.24/1.31  
% 2.24/1.31  Ordering : KBO
% 2.24/1.31  
% 2.24/1.31  Simplification rules
% 2.24/1.31  ----------------------
% 2.24/1.31  #Subsume      : 1
% 2.24/1.31  #Demod        : 48
% 2.24/1.31  #Tautology    : 13
% 2.24/1.31  #SimpNegUnit  : 2
% 2.24/1.31  #BackRed      : 0
% 2.24/1.31  
% 2.24/1.31  #Partial instantiations: 0
% 2.24/1.31  #Strategies tried      : 1
% 2.24/1.31  
% 2.24/1.31  Timing (in seconds)
% 2.24/1.31  ----------------------
% 2.24/1.31  Preprocessing        : 0.28
% 2.24/1.31  Parsing              : 0.16
% 2.24/1.31  CNF conversion       : 0.02
% 2.24/1.31  Main loop            : 0.23
% 2.24/1.31  Inferencing          : 0.09
% 2.24/1.31  Reduction            : 0.06
% 2.24/1.31  Demodulation         : 0.05
% 2.24/1.31  BG Simplification    : 0.01
% 2.24/1.31  Subsumption          : 0.05
% 2.24/1.31  Abstraction          : 0.01
% 2.24/1.31  MUC search           : 0.00
% 2.24/1.31  Cooper               : 0.00
% 2.24/1.31  Total                : 0.55
% 2.24/1.31  Index Insertion      : 0.00
% 2.24/1.31  Index Deletion       : 0.00
% 2.24/1.31  Index Matching       : 0.00
% 2.24/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
