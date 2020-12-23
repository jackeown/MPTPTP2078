%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:33 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 212 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  122 ( 468 expanded)
%              Number of equality atoms :   17 (  71 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_26,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [A_24] :
      ( u1_struct_0(A_24) = k2_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

tff(c_46,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_47,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_28])).

tff(c_52,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_52])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_29] :
      ( m1_subset_1('#skF_1'(A_29),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_71,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_tops_1('#skF_1'(A_10),A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    ! [B_38,A_39] :
      ( v1_tops_1(B_38,A_39)
      | k2_pre_topc(A_39,B_38) != k2_struct_0(A_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [B_38] :
      ( v1_tops_1(B_38,'#skF_2')
      | k2_pre_topc('#skF_2',B_38) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_113])).

tff(c_132,plain,(
    ! [B_40] :
      ( v1_tops_1(B_40,'#skF_2')
      | k2_pre_topc('#skF_2',B_40) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_126])).

tff(c_147,plain,
    ( v1_tops_1('#skF_1'('#skF_2'),'#skF_2')
    | k2_pre_topc('#skF_2','#skF_1'('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_132])).

tff(c_170,plain,(
    k2_pre_topc('#skF_2','#skF_1'('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_150,plain,(
    ! [A_41,B_42] :
      ( k2_pre_topc(A_41,B_42) = k2_struct_0(A_41)
      | ~ v1_tops_1(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_163,plain,(
    ! [B_42] :
      ( k2_pre_topc('#skF_2',B_42) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_42,'#skF_2')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_150])).

tff(c_171,plain,(
    ! [B_43] :
      ( k2_pre_topc('#skF_2',B_43) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_163])).

tff(c_186,plain,
    ( k2_pre_topc('#skF_2','#skF_1'('#skF_2')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_1'('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_171])).

tff(c_191,plain,(
    ~ v1_tops_1('#skF_1'('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_186])).

tff(c_194,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_194])).

tff(c_200,plain,(
    k2_pre_topc('#skF_2','#skF_1'('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_8])).

tff(c_223,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_71,c_46,c_46,c_213])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_tops_1(A_12,k2_struct_0(A_12)) = k2_struct_0(A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_225,plain,(
    ! [C_44,A_45,B_46] :
      ( m2_connsp_2(C_44,A_45,B_46)
      | ~ r1_tarski(B_46,k1_tops_1(A_45,C_44))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_880,plain,(
    ! [A_103,B_104] :
      ( m2_connsp_2(k2_struct_0(A_103),A_103,B_104)
      | ~ r1_tarski(B_104,k2_struct_0(A_103))
      | ~ m1_subset_1(k2_struct_0(A_103),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_225])).

tff(c_887,plain,(
    ! [B_104] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_104)
      | ~ r1_tarski(B_104,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_880])).

tff(c_892,plain,(
    ! [B_105] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_105)
      | ~ r1_tarski(B_105,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_32,c_30,c_46,c_223,c_887])).

tff(c_908,plain,
    ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_892])).

tff(c_919,plain,(
    m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_908])).

tff(c_921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.55  
% 3.10/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.56  %$ m2_connsp_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.10/1.56  
% 3.10/1.56  %Foreground sorts:
% 3.10/1.56  
% 3.10/1.56  
% 3.10/1.56  %Background operators:
% 3.10/1.56  
% 3.10/1.56  
% 3.10/1.56  %Foreground operators:
% 3.10/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.10/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.10/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.56  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.10/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.10/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.10/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.10/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.10/1.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.10/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.10/1.56  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.10/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.56  
% 3.16/1.57  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.16/1.57  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.16/1.57  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.16/1.57  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.57  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_tops_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_tops_1)).
% 3.16/1.57  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.16/1.57  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.16/1.57  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 3.16/1.57  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.16/1.57  tff(c_26, plain, (~m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.57  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.57  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.57  tff(c_36, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.57  tff(c_42, plain, (![A_24]: (u1_struct_0(A_24)=k2_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_10, c_36])).
% 3.16/1.57  tff(c_46, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_42])).
% 3.16/1.57  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.57  tff(c_47, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_28])).
% 3.16/1.57  tff(c_52, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.57  tff(c_56, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_47, c_52])).
% 3.16/1.57  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.57  tff(c_62, plain, (![A_29]: (m1_subset_1('#skF_1'(A_29), k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.57  tff(c_68, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46, c_62])).
% 3.16/1.57  tff(c_71, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_68])).
% 3.16/1.57  tff(c_16, plain, (![A_10]: (v1_tops_1('#skF_1'(A_10), A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.57  tff(c_113, plain, (![B_38, A_39]: (v1_tops_1(B_38, A_39) | k2_pre_topc(A_39, B_38)!=k2_struct_0(A_39) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_126, plain, (![B_38]: (v1_tops_1(B_38, '#skF_2') | k2_pre_topc('#skF_2', B_38)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_38, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_113])).
% 3.16/1.57  tff(c_132, plain, (![B_40]: (v1_tops_1(B_40, '#skF_2') | k2_pre_topc('#skF_2', B_40)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_40, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_126])).
% 3.16/1.57  tff(c_147, plain, (v1_tops_1('#skF_1'('#skF_2'), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_2'))!=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_71, c_132])).
% 3.16/1.57  tff(c_170, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_147])).
% 3.16/1.57  tff(c_150, plain, (![A_41, B_42]: (k2_pre_topc(A_41, B_42)=k2_struct_0(A_41) | ~v1_tops_1(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_163, plain, (![B_42]: (k2_pre_topc('#skF_2', B_42)=k2_struct_0('#skF_2') | ~v1_tops_1(B_42, '#skF_2') | ~m1_subset_1(B_42, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_150])).
% 3.16/1.57  tff(c_171, plain, (![B_43]: (k2_pre_topc('#skF_2', B_43)=k2_struct_0('#skF_2') | ~v1_tops_1(B_43, '#skF_2') | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_163])).
% 3.16/1.57  tff(c_186, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2'))=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_1'('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_71, c_171])).
% 3.16/1.57  tff(c_191, plain, (~v1_tops_1('#skF_1'('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_170, c_186])).
% 3.16/1.57  tff(c_194, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_191])).
% 3.16/1.57  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_194])).
% 3.16/1.57  tff(c_200, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_147])).
% 3.16/1.57  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(k2_pre_topc(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.57  tff(c_213, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_200, c_8])).
% 3.16/1.57  tff(c_223, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_71, c_46, c_46, c_213])).
% 3.16/1.57  tff(c_20, plain, (![A_12]: (k1_tops_1(A_12, k2_struct_0(A_12))=k2_struct_0(A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.57  tff(c_225, plain, (![C_44, A_45, B_46]: (m2_connsp_2(C_44, A_45, B_46) | ~r1_tarski(B_46, k1_tops_1(A_45, C_44)) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.16/1.57  tff(c_880, plain, (![A_103, B_104]: (m2_connsp_2(k2_struct_0(A_103), A_103, B_104) | ~r1_tarski(B_104, k2_struct_0(A_103)) | ~m1_subset_1(k2_struct_0(A_103), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(superposition, [status(thm), theory('equality')], [c_20, c_225])).
% 3.16/1.57  tff(c_887, plain, (![B_104]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_104) | ~r1_tarski(B_104, k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_880])).
% 3.16/1.57  tff(c_892, plain, (![B_105]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_105) | ~r1_tarski(B_105, k2_struct_0('#skF_2')) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_32, c_30, c_46, c_223, c_887])).
% 3.16/1.57  tff(c_908, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_47, c_892])).
% 3.16/1.57  tff(c_919, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_908])).
% 3.16/1.57  tff(c_921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_919])).
% 3.16/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  Inference rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Ref     : 0
% 3.16/1.57  #Sup     : 184
% 3.16/1.57  #Fact    : 0
% 3.16/1.57  #Define  : 0
% 3.16/1.57  #Split   : 9
% 3.16/1.57  #Chain   : 0
% 3.16/1.57  #Close   : 0
% 3.16/1.57  
% 3.16/1.57  Ordering : KBO
% 3.16/1.57  
% 3.16/1.57  Simplification rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Subsume      : 49
% 3.16/1.57  #Demod        : 186
% 3.16/1.57  #Tautology    : 45
% 3.16/1.57  #SimpNegUnit  : 22
% 3.16/1.57  #BackRed      : 1
% 3.16/1.57  
% 3.16/1.57  #Partial instantiations: 0
% 3.16/1.57  #Strategies tried      : 1
% 3.16/1.57  
% 3.16/1.57  Timing (in seconds)
% 3.16/1.57  ----------------------
% 3.16/1.57  Preprocessing        : 0.28
% 3.16/1.57  Parsing              : 0.15
% 3.16/1.57  CNF conversion       : 0.02
% 3.16/1.57  Main loop            : 0.41
% 3.16/1.57  Inferencing          : 0.16
% 3.16/1.57  Reduction            : 0.12
% 3.16/1.57  Demodulation         : 0.08
% 3.16/1.57  BG Simplification    : 0.02
% 3.16/1.57  Subsumption          : 0.08
% 3.16/1.57  Abstraction          : 0.02
% 3.16/1.57  MUC search           : 0.00
% 3.16/1.57  Cooper               : 0.00
% 3.16/1.57  Total                : 0.73
% 3.16/1.57  Index Insertion      : 0.00
% 3.16/1.57  Index Deletion       : 0.00
% 3.16/1.57  Index Matching       : 0.00
% 3.16/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
