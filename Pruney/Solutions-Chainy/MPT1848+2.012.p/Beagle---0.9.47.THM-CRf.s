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
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 873 expanded)
%              Number of leaves         :   20 ( 291 expanded)
%              Depth                    :   16
%              Number of atoms          :  108 (2216 expanded)
%              Number of equality atoms :    9 ( 303 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_37,plain,(
    ! [B_30,A_31] :
      ( l1_pre_topc(B_30)
      | ~ m1_pre_topc(B_30,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_47,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_43])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_pre_topc(A_4,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [B_34] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_34,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_49])).

tff(c_67,plain,(
    ! [B_36] :
      ( m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_36,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_62])).

tff(c_16,plain,(
    ! [B_16] :
      ( ~ v1_subset_1(B_16,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,
    ( ~ v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_16])).

tff(c_81,plain,(
    ~ v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_77,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_67])).

tff(c_82,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_85,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_85])).

tff(c_90,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_332,plain,(
    ! [B_62,A_63] :
      ( v1_subset_1(u1_struct_0(B_62),u1_struct_0(A_63))
      | ~ v1_tex_2(B_62,A_63)
      | ~ m1_subset_1(u1_struct_0(B_62),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_338,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_332])).

tff(c_354,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_338])).

tff(c_355,plain,
    ( ~ v1_tex_2('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_354])).

tff(c_363,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_366,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_363])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_366])).

tff(c_372,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_10,plain,(
    ! [B_11,A_5] :
      ( u1_struct_0(B_11) = '#skF_1'(A_5,B_11)
      | v1_tex_2(B_11,A_5)
      | ~ m1_pre_topc(B_11,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_371,plain,(
    ~ v1_tex_2('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_381,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_371])).

tff(c_392,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_381])).

tff(c_400,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_392])).

tff(c_412,plain,(
    ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_81])).

tff(c_411,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_90])).

tff(c_24,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_350,plain,(
    ! [B_62] :
      ( v1_subset_1(u1_struct_0(B_62),u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_62,'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_62),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_62,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_332])).

tff(c_362,plain,(
    ! [B_62] :
      ( v1_subset_1(u1_struct_0(B_62),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_62,'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_62),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_62,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_350])).

tff(c_716,plain,(
    ! [B_76] :
      ( v1_subset_1(u1_struct_0(B_76),'#skF_1'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_76,'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_76),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3')))
      | ~ m1_pre_topc(B_76,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_362])).

tff(c_728,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_3'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_716])).

tff(c_735,plain,(
    v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_411,c_24,c_400,c_728])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.40  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.40  
% 2.74/1.40  %Foreground sorts:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Background operators:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Foreground operators:
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.74/1.40  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.74/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.74/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.40  
% 2.74/1.42  tff(f_89, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.74/1.42  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.74/1.42  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.74/1.42  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 2.74/1.42  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.74/1.42  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.74/1.42  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 2.74/1.42  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.74/1.42  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.74/1.42  tff(c_37, plain, (![B_30, A_31]: (l1_pre_topc(B_30) | ~m1_pre_topc(B_30, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.42  tff(c_43, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_37])).
% 2.74/1.42  tff(c_47, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_43])).
% 2.74/1.42  tff(c_4, plain, (![A_4]: (m1_pre_topc(A_4, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.74/1.42  tff(c_26, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.74/1.42  tff(c_49, plain, (![B_34, A_35]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.74/1.42  tff(c_62, plain, (![B_34]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_34, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_49])).
% 2.74/1.42  tff(c_67, plain, (![B_36]: (m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_36, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_62])).
% 2.74/1.42  tff(c_16, plain, (![B_16]: (~v1_subset_1(B_16, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.74/1.42  tff(c_74, plain, (~v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_67, c_16])).
% 2.74/1.42  tff(c_81, plain, (~v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74])).
% 2.74/1.42  tff(c_77, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_67])).
% 2.74/1.42  tff(c_82, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_77])).
% 2.74/1.42  tff(c_85, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.74/1.42  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_85])).
% 2.74/1.42  tff(c_90, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_77])).
% 2.74/1.42  tff(c_332, plain, (![B_62, A_63]: (v1_subset_1(u1_struct_0(B_62), u1_struct_0(A_63)) | ~v1_tex_2(B_62, A_63) | ~m1_subset_1(u1_struct_0(B_62), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.74/1.42  tff(c_338, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_tex_2('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_90, c_332])).
% 2.74/1.42  tff(c_354, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_tex_2('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_338])).
% 2.74/1.42  tff(c_355, plain, (~v1_tex_2('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_81, c_354])).
% 2.74/1.42  tff(c_363, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_355])).
% 2.74/1.42  tff(c_366, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_363])).
% 2.74/1.42  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_366])).
% 2.74/1.42  tff(c_372, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_355])).
% 2.74/1.42  tff(c_10, plain, (![B_11, A_5]: (u1_struct_0(B_11)='#skF_1'(A_5, B_11) | v1_tex_2(B_11, A_5) | ~m1_pre_topc(B_11, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.74/1.42  tff(c_371, plain, (~v1_tex_2('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_355])).
% 2.74/1.42  tff(c_381, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_371])).
% 2.74/1.42  tff(c_392, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_381])).
% 2.74/1.42  tff(c_400, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_372, c_392])).
% 2.74/1.42  tff(c_412, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_81])).
% 2.74/1.42  tff(c_411, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_90])).
% 2.74/1.42  tff(c_24, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.74/1.42  tff(c_350, plain, (![B_62]: (v1_subset_1(u1_struct_0(B_62), u1_struct_0('#skF_2')) | ~v1_tex_2(B_62, '#skF_2') | ~m1_subset_1(u1_struct_0(B_62), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_62, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_332])).
% 2.74/1.42  tff(c_362, plain, (![B_62]: (v1_subset_1(u1_struct_0(B_62), u1_struct_0('#skF_3')) | ~v1_tex_2(B_62, '#skF_2') | ~m1_subset_1(u1_struct_0(B_62), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_62, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_350])).
% 2.74/1.42  tff(c_716, plain, (![B_76]: (v1_subset_1(u1_struct_0(B_76), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2(B_76, '#skF_2') | ~m1_subset_1(u1_struct_0(B_76), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))) | ~m1_pre_topc(B_76, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_362])).
% 2.74/1.42  tff(c_728, plain, (v1_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_400, c_716])).
% 2.74/1.42  tff(c_735, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_411, c_24, c_400, c_728])).
% 2.74/1.42  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_735])).
% 2.74/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.42  
% 2.74/1.42  Inference rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Ref     : 0
% 2.74/1.42  #Sup     : 133
% 2.74/1.42  #Fact    : 0
% 2.74/1.42  #Define  : 0
% 2.74/1.42  #Split   : 2
% 2.74/1.42  #Chain   : 0
% 2.74/1.42  #Close   : 0
% 2.74/1.42  
% 2.74/1.42  Ordering : KBO
% 2.74/1.42  
% 2.74/1.42  Simplification rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Subsume      : 30
% 2.74/1.42  #Demod        : 163
% 2.74/1.42  #Tautology    : 39
% 2.74/1.42  #SimpNegUnit  : 8
% 2.74/1.42  #BackRed      : 14
% 2.74/1.42  
% 2.74/1.42  #Partial instantiations: 0
% 2.74/1.42  #Strategies tried      : 1
% 2.74/1.42  
% 2.74/1.42  Timing (in seconds)
% 2.74/1.42  ----------------------
% 2.74/1.42  Preprocessing        : 0.29
% 2.74/1.42  Parsing              : 0.15
% 2.74/1.42  CNF conversion       : 0.02
% 2.74/1.42  Main loop            : 0.31
% 2.74/1.42  Inferencing          : 0.11
% 2.74/1.42  Reduction            : 0.09
% 2.74/1.42  Demodulation         : 0.07
% 2.74/1.42  BG Simplification    : 0.02
% 2.74/1.42  Subsumption          : 0.07
% 2.74/1.42  Abstraction          : 0.02
% 2.74/1.42  MUC search           : 0.00
% 2.74/1.42  Cooper               : 0.00
% 2.74/1.42  Total                : 0.63
% 2.74/1.42  Index Insertion      : 0.00
% 2.74/1.42  Index Deletion       : 0.00
% 2.74/1.42  Index Matching       : 0.00
% 2.74/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
