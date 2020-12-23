%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:08 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 116 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 330 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v2_pre_topc(k1_tex_2(A,B))
             => ( v1_tdlat_3(k1_tex_2(A,B))
                & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) )
       => ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_102,plain,(
    ! [A_26,B_27] :
      ( ~ v2_struct_0(k1_tex_2(A_26,B_27))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_105,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_108,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_105])).

tff(c_109,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_108])).

tff(c_45,plain,(
    ! [A_16,B_17] :
      ( ~ v2_struct_0(k1_tex_2(A_16,B_17))
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_51,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_48])).

tff(c_52,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_51])).

tff(c_24,plain,
    ( ~ v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53,plain,(
    ! [A_18,B_19] :
      ( v7_struct_0(k1_tex_2(A_18,B_19))
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_59,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_56])).

tff(c_60,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_59])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_tdlat_3(A_4)
      | ~ v2_pre_topc(A_4)
      | ~ v7_struct_0(A_4)
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_6])).

tff(c_69,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_63])).

tff(c_70,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_34,c_69])).

tff(c_75,plain,(
    ! [A_20,B_21] :
      ( m1_pre_topc(k1_tex_2(A_20,B_21),A_20)
      | ~ m1_subset_1(B_21,u1_struct_0(A_20))
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_80,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_81,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_80])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( l1_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_87,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_84])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_87])).

tff(c_90,plain,(
    ~ v2_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_110,plain,(
    ! [A_28,B_29] :
      ( v7_struct_0(k1_tex_2(A_28,B_29))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_110])).

tff(c_116,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_113])).

tff(c_117,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_116])).

tff(c_4,plain,(
    ! [A_4] :
      ( v2_tdlat_3(A_4)
      | ~ v2_pre_topc(A_4)
      | ~ v7_struct_0(A_4)
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_120,plain,
    ( v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_126,plain,
    ( v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_120])).

tff(c_127,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_90,c_126])).

tff(c_132,plain,(
    ! [A_30,B_31] :
      ( m1_pre_topc(k1_tex_2(A_30,B_31),A_30)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_134,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_137,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_134])).

tff(c_138,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_137])).

tff(c_141,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_144,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_141])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  %$ m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.97/1.24  
% 1.97/1.24  %Foreground sorts:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Background operators:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Foreground operators:
% 1.97/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.24  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.97/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.97/1.24  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.97/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.24  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.24  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.97/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.97/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.97/1.24  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 1.97/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.24  
% 1.97/1.26  tff(f_93, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tex_2)).
% 1.97/1.26  tff(f_78, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 1.97/1.26  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A)) => (((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_1)).
% 1.97/1.26  tff(f_64, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 1.97/1.26  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 1.97/1.26  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.97/1.26  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.97/1.26  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.97/1.26  tff(c_102, plain, (![A_26, B_27]: (~v2_struct_0(k1_tex_2(A_26, B_27)) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.97/1.26  tff(c_105, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_102])).
% 1.97/1.26  tff(c_108, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_105])).
% 1.97/1.26  tff(c_109, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_108])).
% 1.97/1.26  tff(c_45, plain, (![A_16, B_17]: (~v2_struct_0(k1_tex_2(A_16, B_17)) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.97/1.26  tff(c_48, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_45])).
% 1.97/1.26  tff(c_51, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_48])).
% 1.97/1.26  tff(c_52, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_51])).
% 1.97/1.26  tff(c_24, plain, (~v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.97/1.26  tff(c_34, plain, (~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_24])).
% 1.97/1.26  tff(c_26, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.97/1.26  tff(c_53, plain, (![A_18, B_19]: (v7_struct_0(k1_tex_2(A_18, B_19)) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.97/1.26  tff(c_56, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_53])).
% 1.97/1.26  tff(c_59, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_56])).
% 1.97/1.26  tff(c_60, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_59])).
% 1.97/1.26  tff(c_6, plain, (![A_4]: (v1_tdlat_3(A_4) | ~v2_pre_topc(A_4) | ~v7_struct_0(A_4) | v2_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.26  tff(c_63, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_6])).
% 1.97/1.26  tff(c_69, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_63])).
% 1.97/1.26  tff(c_70, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_34, c_69])).
% 1.97/1.26  tff(c_75, plain, (![A_20, B_21]: (m1_pre_topc(k1_tex_2(A_20, B_21), A_20) | ~m1_subset_1(B_21, u1_struct_0(A_20)) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.26  tff(c_77, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_75])).
% 1.97/1.26  tff(c_80, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_77])).
% 1.97/1.26  tff(c_81, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_80])).
% 1.97/1.26  tff(c_2, plain, (![B_3, A_1]: (l1_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.26  tff(c_84, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_81, c_2])).
% 1.97/1.26  tff(c_87, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_84])).
% 1.97/1.26  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_87])).
% 1.97/1.26  tff(c_90, plain, (~v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_24])).
% 1.97/1.26  tff(c_110, plain, (![A_28, B_29]: (v7_struct_0(k1_tex_2(A_28, B_29)) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.97/1.26  tff(c_113, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_110])).
% 1.97/1.26  tff(c_116, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_113])).
% 1.97/1.26  tff(c_117, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_116])).
% 1.97/1.26  tff(c_4, plain, (![A_4]: (v2_tdlat_3(A_4) | ~v2_pre_topc(A_4) | ~v7_struct_0(A_4) | v2_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.26  tff(c_120, plain, (v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_117, c_4])).
% 1.97/1.26  tff(c_126, plain, (v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_120])).
% 1.97/1.26  tff(c_127, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_109, c_90, c_126])).
% 1.97/1.26  tff(c_132, plain, (![A_30, B_31]: (m1_pre_topc(k1_tex_2(A_30, B_31), A_30) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.26  tff(c_134, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_132])).
% 1.97/1.26  tff(c_137, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_134])).
% 1.97/1.26  tff(c_138, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_137])).
% 1.97/1.26  tff(c_141, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_138, c_2])).
% 1.97/1.26  tff(c_144, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_141])).
% 1.97/1.26  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_144])).
% 1.97/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  
% 1.97/1.26  Inference rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Ref     : 0
% 1.97/1.26  #Sup     : 14
% 1.97/1.26  #Fact    : 0
% 1.97/1.26  #Define  : 0
% 1.97/1.26  #Split   : 1
% 1.97/1.26  #Chain   : 0
% 1.97/1.26  #Close   : 0
% 1.97/1.26  
% 1.97/1.26  Ordering : KBO
% 1.97/1.26  
% 1.97/1.26  Simplification rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Subsume      : 2
% 1.97/1.26  #Demod        : 15
% 1.97/1.26  #Tautology    : 3
% 1.97/1.26  #SimpNegUnit  : 14
% 1.97/1.26  #BackRed      : 0
% 1.97/1.26  
% 1.97/1.26  #Partial instantiations: 0
% 1.97/1.26  #Strategies tried      : 1
% 1.97/1.26  
% 1.97/1.26  Timing (in seconds)
% 1.97/1.26  ----------------------
% 1.97/1.26  Preprocessing        : 0.29
% 1.97/1.26  Parsing              : 0.17
% 1.97/1.26  CNF conversion       : 0.02
% 1.97/1.26  Main loop            : 0.16
% 1.97/1.26  Inferencing          : 0.07
% 1.97/1.26  Reduction            : 0.04
% 1.97/1.26  Demodulation         : 0.03
% 1.97/1.26  BG Simplification    : 0.01
% 1.97/1.26  Subsumption          : 0.02
% 1.97/1.26  Abstraction          : 0.01
% 1.97/1.26  MUC search           : 0.00
% 1.97/1.26  Cooper               : 0.00
% 1.97/1.26  Total                : 0.49
% 1.97/1.26  Index Insertion      : 0.00
% 1.97/1.26  Index Deletion       : 0.00
% 1.97/1.26  Index Matching       : 0.00
% 1.97/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
