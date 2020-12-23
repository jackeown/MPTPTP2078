%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:31 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 167 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 491 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_185,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_188,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_185])).

tff(c_197,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_188])).

tff(c_20,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_191,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_185])).

tff(c_200,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_191])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    ! [B_30,A_31] :
      ( l1_pre_topc(B_30)
      | ~ m1_pre_topc(B_30,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_57])).

tff(c_34,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_90,plain,(
    ! [B_43,A_44] :
      ( r1_tsep_1(B_43,A_44)
      | ~ r1_tsep_1(A_44,B_43)
      | ~ l1_struct_0(B_43)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_93,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_94,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_97,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_94])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_97])).

tff(c_103,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_54])).

tff(c_69,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_102,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_109,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_112,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_112])).

tff(c_118,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_104,plain,(
    ! [B_45,A_46] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,(
    ! [A_39,A_3] :
      ( r1_tarski(A_39,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_39,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_88,plain,(
    ! [A_39,A_3] :
      ( r1_tarski(A_39,A_3)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_85])).

tff(c_108,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(u1_struct_0(B_45),u1_struct_0(A_46))
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_104,c_88])).

tff(c_125,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(u1_struct_0(A_49),u1_struct_0(B_50))
      | ~ r1_tsep_1(A_49,B_50)
      | ~ l1_struct_0(B_50)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r1_tarski(B_2,A_1)
      | v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [A_63,B_64] :
      ( ~ r1_tarski(u1_struct_0(A_63),u1_struct_0(B_64))
      | v1_xboole_0(u1_struct_0(A_63))
      | ~ r1_tsep_1(A_63,B_64)
      | ~ l1_struct_0(B_64)
      | ~ l1_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_163,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(u1_struct_0(B_65))
      | ~ r1_tsep_1(B_65,A_66)
      | ~ l1_struct_0(A_66)
      | ~ l1_struct_0(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_108,c_158])).

tff(c_167,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_163])).

tff(c_173,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_36,c_103,c_118,c_167])).

tff(c_24,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_176,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_24])).

tff(c_179,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_176])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_179])).

tff(c_183,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_182,plain,(
    r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_221,plain,(
    ! [B_81,A_82] :
      ( r1_tsep_1(B_81,A_82)
      | ~ r1_tsep_1(A_82,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_223,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_182,c_221])).

tff(c_226,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_223])).

tff(c_227,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_230,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_227])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_230])).

tff(c_235,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_239,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_235])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.27  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.20/1.27  
% 2.20/1.27  %Foreground sorts:
% 2.20/1.27  
% 2.20/1.27  
% 2.20/1.27  %Background operators:
% 2.20/1.27  
% 2.20/1.27  
% 2.20/1.27  %Foreground operators:
% 2.20/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.20/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.20/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.20/1.27  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.20/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.27  
% 2.20/1.29  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.20/1.29  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.20/1.29  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.20/1.29  tff(f_85, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.20/1.29  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.20/1.29  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.20/1.29  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.20/1.29  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.20/1.29  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.20/1.29  tff(f_33, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.20/1.29  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.20/1.29  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.29  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.29  tff(c_185, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.29  tff(c_188, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_185])).
% 2.20/1.29  tff(c_197, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_188])).
% 2.20/1.29  tff(c_20, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.29  tff(c_38, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.29  tff(c_191, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_185])).
% 2.20/1.29  tff(c_200, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_191])).
% 2.20/1.29  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.29  tff(c_54, plain, (![B_30, A_31]: (l1_pre_topc(B_30) | ~m1_pre_topc(B_30, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.29  tff(c_57, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.20/1.29  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_57])).
% 2.20/1.29  tff(c_34, plain, (r1_tsep_1('#skF_5', '#skF_4') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.29  tff(c_52, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 2.20/1.29  tff(c_90, plain, (![B_43, A_44]: (r1_tsep_1(B_43, A_44) | ~r1_tsep_1(A_44, B_43) | ~l1_struct_0(B_43) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.29  tff(c_93, plain, (r1_tsep_1('#skF_5', '#skF_4') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_90])).
% 2.20/1.29  tff(c_94, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_93])).
% 2.20/1.29  tff(c_97, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_94])).
% 2.20/1.29  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_97])).
% 2.20/1.29  tff(c_103, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_93])).
% 2.20/1.29  tff(c_60, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_54])).
% 2.20/1.29  tff(c_69, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_60])).
% 2.20/1.29  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.29  tff(c_102, plain, (~l1_struct_0('#skF_5') | r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_93])).
% 2.20/1.29  tff(c_109, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_102])).
% 2.20/1.29  tff(c_112, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_109])).
% 2.20/1.29  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_112])).
% 2.20/1.29  tff(c_118, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_102])).
% 2.20/1.29  tff(c_104, plain, (![B_45, A_46]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.20/1.29  tff(c_16, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.29  tff(c_81, plain, (![A_39, B_40]: (r2_hidden(A_39, B_40) | v1_xboole_0(B_40) | ~m1_subset_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.29  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.29  tff(c_85, plain, (![A_39, A_3]: (r1_tarski(A_39, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_39, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_81, c_4])).
% 2.20/1.29  tff(c_88, plain, (![A_39, A_3]: (r1_tarski(A_39, A_3) | ~m1_subset_1(A_39, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_16, c_85])).
% 2.20/1.29  tff(c_108, plain, (![B_45, A_46]: (r1_tarski(u1_struct_0(B_45), u1_struct_0(A_46)) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_104, c_88])).
% 2.20/1.29  tff(c_125, plain, (![A_49, B_50]: (r1_xboole_0(u1_struct_0(A_49), u1_struct_0(B_50)) | ~r1_tsep_1(A_49, B_50) | ~l1_struct_0(B_50) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.20/1.29  tff(c_2, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1) | ~r1_tarski(B_2, A_1) | v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.29  tff(c_158, plain, (![A_63, B_64]: (~r1_tarski(u1_struct_0(A_63), u1_struct_0(B_64)) | v1_xboole_0(u1_struct_0(A_63)) | ~r1_tsep_1(A_63, B_64) | ~l1_struct_0(B_64) | ~l1_struct_0(A_63))), inference(resolution, [status(thm)], [c_125, c_2])).
% 2.20/1.29  tff(c_163, plain, (![B_65, A_66]: (v1_xboole_0(u1_struct_0(B_65)) | ~r1_tsep_1(B_65, A_66) | ~l1_struct_0(A_66) | ~l1_struct_0(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_108, c_158])).
% 2.20/1.29  tff(c_167, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_52, c_163])).
% 2.20/1.29  tff(c_173, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_36, c_103, c_118, c_167])).
% 2.20/1.29  tff(c_24, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.29  tff(c_176, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_173, c_24])).
% 2.20/1.29  tff(c_179, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_176])).
% 2.20/1.29  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_179])).
% 2.20/1.29  tff(c_183, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 2.20/1.29  tff(c_182, plain, (r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.20/1.29  tff(c_221, plain, (![B_81, A_82]: (r1_tsep_1(B_81, A_82) | ~r1_tsep_1(A_82, B_81) | ~l1_struct_0(B_81) | ~l1_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.29  tff(c_223, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_182, c_221])).
% 2.20/1.29  tff(c_226, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_183, c_223])).
% 2.20/1.29  tff(c_227, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_226])).
% 2.20/1.29  tff(c_230, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_227])).
% 2.20/1.29  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_230])).
% 2.20/1.29  tff(c_235, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_226])).
% 2.20/1.29  tff(c_239, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_235])).
% 2.20/1.29  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_239])).
% 2.20/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  Inference rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Ref     : 0
% 2.20/1.29  #Sup     : 28
% 2.20/1.29  #Fact    : 0
% 2.20/1.29  #Define  : 0
% 2.20/1.29  #Split   : 4
% 2.20/1.29  #Chain   : 0
% 2.20/1.29  #Close   : 0
% 2.20/1.29  
% 2.20/1.29  Ordering : KBO
% 2.20/1.29  
% 2.20/1.29  Simplification rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Subsume      : 0
% 2.20/1.29  #Demod        : 23
% 2.20/1.29  #Tautology    : 6
% 2.20/1.29  #SimpNegUnit  : 4
% 2.20/1.29  #BackRed      : 0
% 2.20/1.29  
% 2.20/1.29  #Partial instantiations: 0
% 2.20/1.29  #Strategies tried      : 1
% 2.20/1.29  
% 2.20/1.29  Timing (in seconds)
% 2.20/1.29  ----------------------
% 2.20/1.29  Preprocessing        : 0.31
% 2.20/1.29  Parsing              : 0.18
% 2.20/1.29  CNF conversion       : 0.02
% 2.20/1.29  Main loop            : 0.20
% 2.20/1.29  Inferencing          : 0.08
% 2.20/1.29  Reduction            : 0.05
% 2.20/1.29  Demodulation         : 0.04
% 2.20/1.29  BG Simplification    : 0.01
% 2.20/1.29  Subsumption          : 0.03
% 2.20/1.29  Abstraction          : 0.01
% 2.20/1.29  MUC search           : 0.00
% 2.20/1.29  Cooper               : 0.00
% 2.20/1.29  Total                : 0.55
% 2.20/1.29  Index Insertion      : 0.00
% 2.20/1.29  Index Deletion       : 0.00
% 2.20/1.29  Index Matching       : 0.00
% 2.20/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
