%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:18 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   61 (  91 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 216 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_49,plain,(
    ! [A_42] :
      ( m1_subset_1(u1_orders_2(A_42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_42),u1_struct_0(A_42))))
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    ! [A_42] :
      ( v1_relat_1(u1_orders_2(A_42))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_42),u1_struct_0(A_42)))
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_49,c_4])).

tff(c_55,plain,(
    ! [A_42] :
      ( v1_relat_1(u1_orders_2(A_42))
      | ~ l1_orders_2(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_28,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_19] :
      ( r1_relat_2(u1_orders_2(A_19),u1_struct_0(A_19))
      | ~ v3_orders_2(A_19)
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [C_44,A_45,B_46] :
      ( r2_hidden(k4_tarski(C_44,C_44),A_45)
      | ~ r2_hidden(C_44,B_46)
      | ~ r1_relat_2(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    ! [A_49,A_50,B_51] :
      ( r2_hidden(k4_tarski(A_49,A_49),A_50)
      | ~ r1_relat_2(A_50,B_51)
      | ~ v1_relat_1(A_50)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_49,B_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_107,plain,(
    ! [A_63,A_64] :
      ( r2_hidden(k4_tarski(A_63,A_63),u1_orders_2(A_64))
      | ~ v1_relat_1(u1_orders_2(A_64))
      | v1_xboole_0(u1_struct_0(A_64))
      | ~ m1_subset_1(A_63,u1_struct_0(A_64))
      | ~ v3_orders_2(A_64)
      | ~ l1_orders_2(A_64) ) ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_20,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_orders_2(A_20,B_24,C_26)
      | ~ r2_hidden(k4_tarski(B_24,C_26),u1_orders_2(A_20))
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_120,plain,(
    ! [A_65,A_66] :
      ( r1_orders_2(A_65,A_66,A_66)
      | ~ v1_relat_1(u1_orders_2(A_65))
      | v1_xboole_0(u1_struct_0(A_65))
      | ~ m1_subset_1(A_66,u1_struct_0(A_65))
      | ~ v3_orders_2(A_65)
      | ~ l1_orders_2(A_65) ) ),
    inference(resolution,[status(thm)],[c_107,c_20])).

tff(c_122,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v3_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_125,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_122])).

tff(c_126,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_125])).

tff(c_127,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_131,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_127])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_131])).

tff(c_136,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_14,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_136,c_14])).

tff(c_143,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_140])).

tff(c_146,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_143])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.27  
% 2.00/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.27  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.27  
% 2.00/1.27  %Foreground sorts:
% 2.00/1.27  
% 2.00/1.27  
% 2.00/1.27  %Background operators:
% 2.00/1.27  
% 2.00/1.27  
% 2.00/1.27  %Foreground operators:
% 2.00/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.00/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.00/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.27  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.00/1.27  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.00/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.00/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.00/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.27  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.00/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.00/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.27  
% 2.18/1.29  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 2.18/1.29  tff(f_80, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.18/1.29  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.29  tff(f_84, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.18/1.29  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.29  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_orders_2)).
% 2.18/1.29  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.18/1.29  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 2.18/1.29  tff(f_76, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.18/1.29  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.18/1.29  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.29  tff(c_24, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.29  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.29  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.29  tff(c_49, plain, (![A_42]: (m1_subset_1(u1_orders_2(A_42), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_42), u1_struct_0(A_42)))) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.18/1.29  tff(c_4, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.29  tff(c_52, plain, (![A_42]: (v1_relat_1(u1_orders_2(A_42)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_42), u1_struct_0(A_42))) | ~l1_orders_2(A_42))), inference(resolution, [status(thm)], [c_49, c_4])).
% 2.18/1.29  tff(c_55, plain, (![A_42]: (v1_relat_1(u1_orders_2(A_42)) | ~l1_orders_2(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_52])).
% 2.18/1.29  tff(c_28, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.29  tff(c_34, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.29  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.29  tff(c_18, plain, (![A_19]: (r1_relat_2(u1_orders_2(A_19), u1_struct_0(A_19)) | ~v3_orders_2(A_19) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.29  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.29  tff(c_57, plain, (![C_44, A_45, B_46]: (r2_hidden(k4_tarski(C_44, C_44), A_45) | ~r2_hidden(C_44, B_46) | ~r1_relat_2(A_45, B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.29  tff(c_70, plain, (![A_49, A_50, B_51]: (r2_hidden(k4_tarski(A_49, A_49), A_50) | ~r1_relat_2(A_50, B_51) | ~v1_relat_1(A_50) | v1_xboole_0(B_51) | ~m1_subset_1(A_49, B_51))), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.18/1.29  tff(c_107, plain, (![A_63, A_64]: (r2_hidden(k4_tarski(A_63, A_63), u1_orders_2(A_64)) | ~v1_relat_1(u1_orders_2(A_64)) | v1_xboole_0(u1_struct_0(A_64)) | ~m1_subset_1(A_63, u1_struct_0(A_64)) | ~v3_orders_2(A_64) | ~l1_orders_2(A_64))), inference(resolution, [status(thm)], [c_18, c_70])).
% 2.18/1.29  tff(c_20, plain, (![A_20, B_24, C_26]: (r1_orders_2(A_20, B_24, C_26) | ~r2_hidden(k4_tarski(B_24, C_26), u1_orders_2(A_20)) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.18/1.29  tff(c_120, plain, (![A_65, A_66]: (r1_orders_2(A_65, A_66, A_66) | ~v1_relat_1(u1_orders_2(A_65)) | v1_xboole_0(u1_struct_0(A_65)) | ~m1_subset_1(A_66, u1_struct_0(A_65)) | ~v3_orders_2(A_65) | ~l1_orders_2(A_65))), inference(resolution, [status(thm)], [c_107, c_20])).
% 2.18/1.29  tff(c_122, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v3_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_30, c_120])).
% 2.18/1.29  tff(c_125, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_122])).
% 2.18/1.29  tff(c_126, plain, (~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_125])).
% 2.18/1.29  tff(c_127, plain, (~v1_relat_1(u1_orders_2('#skF_2'))), inference(splitLeft, [status(thm)], [c_126])).
% 2.18/1.29  tff(c_131, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_55, c_127])).
% 2.18/1.29  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_131])).
% 2.18/1.29  tff(c_136, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_126])).
% 2.18/1.29  tff(c_14, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.29  tff(c_140, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_136, c_14])).
% 2.18/1.29  tff(c_143, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_140])).
% 2.18/1.29  tff(c_146, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_24, c_143])).
% 2.18/1.29  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_146])).
% 2.18/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 20
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 1
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 0
% 2.18/1.29  #Demod        : 5
% 2.18/1.29  #Tautology    : 3
% 2.18/1.29  #SimpNegUnit  : 2
% 2.18/1.29  #BackRed      : 0
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.28
% 2.18/1.29  Parsing              : 0.16
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.22
% 2.18/1.29  Inferencing          : 0.10
% 2.18/1.29  Reduction            : 0.05
% 2.18/1.29  Demodulation         : 0.04
% 2.18/1.29  BG Simplification    : 0.01
% 2.18/1.29  Subsumption          : 0.03
% 2.18/1.29  Abstraction          : 0.01
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.54
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
