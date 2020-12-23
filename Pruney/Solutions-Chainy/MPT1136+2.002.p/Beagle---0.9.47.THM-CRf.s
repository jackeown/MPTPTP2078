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
% DateTime   : Thu Dec  3 10:19:17 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 209 expanded)
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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    ! [A_39] :
      ( m1_subset_1(u1_orders_2(A_39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39),u1_struct_0(A_39))))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [C_15,A_13,B_14] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [A_39] :
      ( v1_relat_1(u1_orders_2(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(resolution,[status(thm)],[c_46,c_10])).

tff(c_26,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_17] :
      ( r1_relat_2(u1_orders_2(A_17),u1_struct_0(A_17))
      | ~ v3_orders_2(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [C_41,A_42,B_43] :
      ( r2_hidden(k4_tarski(C_41,C_41),A_42)
      | ~ r2_hidden(C_41,B_43)
      | ~ r1_relat_2(A_42,B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [A_46,A_47,B_48] :
      ( r2_hidden(k4_tarski(A_46,A_46),A_47)
      | ~ r1_relat_2(A_47,B_48)
      | ~ v1_relat_1(A_47)
      | v1_xboole_0(B_48)
      | ~ m1_subset_1(A_46,B_48) ) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_102,plain,(
    ! [A_60,A_61] :
      ( r2_hidden(k4_tarski(A_60,A_60),u1_orders_2(A_61))
      | ~ v1_relat_1(u1_orders_2(A_61))
      | v1_xboole_0(u1_struct_0(A_61))
      | ~ m1_subset_1(A_60,u1_struct_0(A_61))
      | ~ v3_orders_2(A_61)
      | ~ l1_orders_2(A_61) ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_18,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_orders_2(A_18,B_22,C_24)
      | ~ r2_hidden(k4_tarski(B_22,C_24),u1_orders_2(A_18))
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ m1_subset_1(B_22,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_115,plain,(
    ! [A_62,A_63] :
      ( r1_orders_2(A_62,A_63,A_63)
      | ~ v1_relat_1(u1_orders_2(A_62))
      | v1_xboole_0(u1_struct_0(A_62))
      | ~ m1_subset_1(A_63,u1_struct_0(A_62))
      | ~ v3_orders_2(A_62)
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_102,c_18])).

tff(c_117,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v3_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_120,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_117])).

tff(c_121,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_120])).

tff(c_122,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_125,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_12,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_12])).

tff(c_138,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_135])).

tff(c_141,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.26  
% 1.98/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.26  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.26  
% 1.98/1.26  %Foreground sorts:
% 1.98/1.26  
% 1.98/1.26  
% 1.98/1.26  %Background operators:
% 1.98/1.26  
% 1.98/1.26  
% 1.98/1.26  %Foreground operators:
% 1.98/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.98/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.26  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.98/1.26  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 1.98/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.98/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.98/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.26  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.98/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.26  
% 1.98/1.27  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 1.98/1.27  tff(f_75, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 1.98/1.27  tff(f_79, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 1.98/1.27  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.98/1.27  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_orders_2)).
% 1.98/1.27  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.98/1.27  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 1.98/1.27  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 1.98/1.27  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.98/1.27  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.27  tff(c_22, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.27  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.27  tff(c_46, plain, (![A_39]: (m1_subset_1(u1_orders_2(A_39), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39), u1_struct_0(A_39)))) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.98/1.27  tff(c_10, plain, (![C_15, A_13, B_14]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.27  tff(c_50, plain, (![A_39]: (v1_relat_1(u1_orders_2(A_39)) | ~l1_orders_2(A_39))), inference(resolution, [status(thm)], [c_46, c_10])).
% 1.98/1.27  tff(c_26, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.27  tff(c_32, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.27  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.27  tff(c_16, plain, (![A_17]: (r1_relat_2(u1_orders_2(A_17), u1_struct_0(A_17)) | ~v3_orders_2(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.98/1.27  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.27  tff(c_52, plain, (![C_41, A_42, B_43]: (r2_hidden(k4_tarski(C_41, C_41), A_42) | ~r2_hidden(C_41, B_43) | ~r1_relat_2(A_42, B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.27  tff(c_65, plain, (![A_46, A_47, B_48]: (r2_hidden(k4_tarski(A_46, A_46), A_47) | ~r1_relat_2(A_47, B_48) | ~v1_relat_1(A_47) | v1_xboole_0(B_48) | ~m1_subset_1(A_46, B_48))), inference(resolution, [status(thm)], [c_2, c_52])).
% 1.98/1.27  tff(c_102, plain, (![A_60, A_61]: (r2_hidden(k4_tarski(A_60, A_60), u1_orders_2(A_61)) | ~v1_relat_1(u1_orders_2(A_61)) | v1_xboole_0(u1_struct_0(A_61)) | ~m1_subset_1(A_60, u1_struct_0(A_61)) | ~v3_orders_2(A_61) | ~l1_orders_2(A_61))), inference(resolution, [status(thm)], [c_16, c_65])).
% 1.98/1.27  tff(c_18, plain, (![A_18, B_22, C_24]: (r1_orders_2(A_18, B_22, C_24) | ~r2_hidden(k4_tarski(B_22, C_24), u1_orders_2(A_18)) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~m1_subset_1(B_22, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.27  tff(c_115, plain, (![A_62, A_63]: (r1_orders_2(A_62, A_63, A_63) | ~v1_relat_1(u1_orders_2(A_62)) | v1_xboole_0(u1_struct_0(A_62)) | ~m1_subset_1(A_63, u1_struct_0(A_62)) | ~v3_orders_2(A_62) | ~l1_orders_2(A_62))), inference(resolution, [status(thm)], [c_102, c_18])).
% 1.98/1.27  tff(c_117, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v3_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_28, c_115])).
% 1.98/1.27  tff(c_120, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_117])).
% 1.98/1.27  tff(c_121, plain, (~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_120])).
% 1.98/1.27  tff(c_122, plain, (~v1_relat_1(u1_orders_2('#skF_2'))), inference(splitLeft, [status(thm)], [c_121])).
% 1.98/1.27  tff(c_125, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_50, c_122])).
% 1.98/1.27  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_125])).
% 1.98/1.27  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_121])).
% 1.98/1.27  tff(c_12, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.98/1.27  tff(c_135, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_130, c_12])).
% 1.98/1.27  tff(c_138, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_135])).
% 1.98/1.27  tff(c_141, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_22, c_138])).
% 1.98/1.27  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_141])).
% 1.98/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  Inference rules
% 1.98/1.27  ----------------------
% 1.98/1.27  #Ref     : 0
% 1.98/1.27  #Sup     : 20
% 1.98/1.27  #Fact    : 0
% 1.98/1.27  #Define  : 0
% 1.98/1.27  #Split   : 1
% 1.98/1.27  #Chain   : 0
% 1.98/1.27  #Close   : 0
% 1.98/1.27  
% 1.98/1.27  Ordering : KBO
% 1.98/1.27  
% 1.98/1.27  Simplification rules
% 1.98/1.27  ----------------------
% 1.98/1.27  #Subsume      : 0
% 1.98/1.27  #Demod        : 4
% 1.98/1.27  #Tautology    : 3
% 1.98/1.27  #SimpNegUnit  : 2
% 1.98/1.27  #BackRed      : 0
% 1.98/1.27  
% 1.98/1.27  #Partial instantiations: 0
% 1.98/1.27  #Strategies tried      : 1
% 1.98/1.27  
% 1.98/1.27  Timing (in seconds)
% 1.98/1.27  ----------------------
% 1.98/1.28  Preprocessing        : 0.29
% 1.98/1.28  Parsing              : 0.17
% 1.98/1.28  CNF conversion       : 0.02
% 1.98/1.28  Main loop            : 0.18
% 1.98/1.28  Inferencing          : 0.08
% 1.98/1.28  Reduction            : 0.04
% 1.98/1.28  Demodulation         : 0.03
% 1.98/1.28  BG Simplification    : 0.01
% 1.98/1.28  Subsumption          : 0.03
% 1.98/1.28  Abstraction          : 0.01
% 1.98/1.28  MUC search           : 0.00
% 1.98/1.28  Cooper               : 0.00
% 1.98/1.28  Total                : 0.50
% 1.98/1.28  Index Insertion      : 0.00
% 1.98/1.28  Index Deletion       : 0.00
% 1.98/1.28  Index Matching       : 0.00
% 1.98/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
