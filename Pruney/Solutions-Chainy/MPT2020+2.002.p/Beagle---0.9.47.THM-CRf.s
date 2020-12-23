%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:10 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 297 expanded)
%              Number of leaves         :   22 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  145 ( 986 expanded)
%              Number of equality atoms :   22 ( 260 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v1_tops_2(C,A) )
                     => v1_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_24,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ~ v1_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_35,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_18,plain,(
    ! [A_11,B_17] :
      ( m1_subset_1('#skF_1'(A_11,B_17),k1_zfmisc_1(u1_struct_0(A_11)))
      | v1_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_59,plain,(
    ! [C_37,A_38,D_39,B_40] :
      ( C_37 = A_38
      | g1_pre_topc(C_37,D_39) != g1_pre_topc(A_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,(
    ! [A_52,B_53] :
      ( u1_struct_0('#skF_2') = A_52
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_59])).

tff(c_107,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_114,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_107])).

tff(c_116,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_114])).

tff(c_22,plain,(
    v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_66,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),B_46)
      | v1_tops_2(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45))))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_72,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_66])).

tff(c_79,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_72])).

tff(c_80,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_79])).

tff(c_244,plain,(
    ! [C_63,A_64,B_65] :
      ( v3_pre_topc(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ v1_tops_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64))))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_374,plain,(
    ! [A_76] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_76)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ v1_tops_2('#skF_4',A_76)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_76))))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_80,c_244])).

tff(c_377,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v1_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_374])).

tff(c_383,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35,c_116,c_22,c_377])).

tff(c_388,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_391,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_388])).

tff(c_394,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_35,c_391])).

tff(c_396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_394])).

tff(c_397,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_398,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_154,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6])).

tff(c_166,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_154])).

tff(c_50,plain,(
    ! [D_33,B_34,C_35,A_36] :
      ( D_33 = B_34
      | g1_pre_topc(C_35,D_33) != g1_pre_topc(A_36,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [D_33,C_35] :
      ( u1_pre_topc('#skF_2') = D_33
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_35,D_33)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_50])).

tff(c_195,plain,(
    ! [D_33,C_35] :
      ( u1_pre_topc('#skF_2') = D_33
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_35,D_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_116,c_54])).

tff(c_198,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_195])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ v3_pre_topc(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_148,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_3,'#skF_2')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_4])).

tff(c_162,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_3,'#skF_2')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148])).

tff(c_275,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_3,'#skF_2')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_162])).

tff(c_422,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_398,c_275])).

tff(c_437,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_422])).

tff(c_125,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1('#skF_1'(A_55,B_56),k1_zfmisc_1(u1_struct_0(A_55)))
      | v1_tops_2(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [A_55,B_56] :
      ( v3_pre_topc('#skF_1'(A_55,B_56),A_55)
      | ~ r2_hidden('#skF_1'(A_55,B_56),u1_pre_topc(A_55))
      | v1_tops_2(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_447,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_437,c_133])).

tff(c_452,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_35,c_447])).

tff(c_453,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_452])).

tff(c_14,plain,(
    ! [A_11,B_17] :
      ( ~ v3_pre_topc('#skF_1'(A_11,B_17),A_11)
      | v1_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_456,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_453,c_14])).

tff(c_459,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_35,c_456])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:47:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.30  
% 2.43/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.30  %$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.43/1.30  
% 2.43/1.30  %Foreground sorts:
% 2.43/1.30  
% 2.43/1.30  
% 2.43/1.30  %Background operators:
% 2.43/1.30  
% 2.43/1.30  
% 2.43/1.30  %Foreground operators:
% 2.43/1.30  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.43/1.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.43/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.30  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.43/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.30  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.43/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.30  
% 2.43/1.32  tff(f_81, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v1_tops_2(C, A)) => v1_tops_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_waybel_9)).
% 2.43/1.32  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 2.43/1.32  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.43/1.32  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.43/1.32  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.43/1.32  tff(c_24, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.32  tff(c_20, plain, (~v1_tops_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.32  tff(c_36, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20])).
% 2.43/1.32  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.32  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.32  tff(c_35, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.43/1.32  tff(c_18, plain, (![A_11, B_17]: (m1_subset_1('#skF_1'(A_11, B_17), k1_zfmisc_1(u1_struct_0(A_11))) | v1_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.32  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.32  tff(c_6, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.43/1.32  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.32  tff(c_59, plain, (![C_37, A_38, D_39, B_40]: (C_37=A_38 | g1_pre_topc(C_37, D_39)!=g1_pre_topc(A_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.43/1.32  tff(c_97, plain, (![A_52, B_53]: (u1_struct_0('#skF_2')=A_52 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_59])).
% 2.43/1.32  tff(c_107, plain, (![A_4]: (u1_struct_0(A_4)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_6, c_97])).
% 2.43/1.32  tff(c_114, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_107])).
% 2.43/1.32  tff(c_116, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_114])).
% 2.43/1.32  tff(c_22, plain, (v1_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.32  tff(c_66, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), B_46) | v1_tops_2(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45)))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.32  tff(c_72, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_35, c_66])).
% 2.43/1.32  tff(c_79, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_72])).
% 2.43/1.32  tff(c_80, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_79])).
% 2.43/1.32  tff(c_244, plain, (![C_63, A_64, B_65]: (v3_pre_topc(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~v1_tops_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64)))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.32  tff(c_374, plain, (![A_76]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_76) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_76))) | ~v1_tops_2('#skF_4', A_76) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_76)))) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_80, c_244])).
% 2.43/1.32  tff(c_377, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tops_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116, c_374])).
% 2.43/1.32  tff(c_383, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_35, c_116, c_22, c_377])).
% 2.43/1.32  tff(c_388, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_383])).
% 2.43/1.32  tff(c_391, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_388])).
% 2.43/1.32  tff(c_394, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_35, c_391])).
% 2.43/1.32  tff(c_396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_394])).
% 2.43/1.32  tff(c_397, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_383])).
% 2.43/1.32  tff(c_398, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_383])).
% 2.43/1.32  tff(c_154, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116, c_6])).
% 2.43/1.32  tff(c_166, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_154])).
% 2.43/1.32  tff(c_50, plain, (![D_33, B_34, C_35, A_36]: (D_33=B_34 | g1_pre_topc(C_35, D_33)!=g1_pre_topc(A_36, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.43/1.32  tff(c_54, plain, (![D_33, C_35]: (u1_pre_topc('#skF_2')=D_33 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_35, D_33) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_50])).
% 2.43/1.32  tff(c_195, plain, (![D_33, C_35]: (u1_pre_topc('#skF_2')=D_33 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_35, D_33))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_116, c_54])).
% 2.43/1.32  tff(c_198, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_195])).
% 2.43/1.32  tff(c_4, plain, (![B_3, A_1]: (r2_hidden(B_3, u1_pre_topc(A_1)) | ~v3_pre_topc(B_3, A_1) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.32  tff(c_148, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_3, '#skF_2') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_4])).
% 2.43/1.32  tff(c_162, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_3, '#skF_2') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_148])).
% 2.43/1.32  tff(c_275, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_3, '#skF_2') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_162])).
% 2.43/1.32  tff(c_422, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_398, c_275])).
% 2.43/1.32  tff(c_437, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_422])).
% 2.43/1.32  tff(c_125, plain, (![A_55, B_56]: (m1_subset_1('#skF_1'(A_55, B_56), k1_zfmisc_1(u1_struct_0(A_55))) | v1_tops_2(B_56, A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.32  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.32  tff(c_133, plain, (![A_55, B_56]: (v3_pre_topc('#skF_1'(A_55, B_56), A_55) | ~r2_hidden('#skF_1'(A_55, B_56), u1_pre_topc(A_55)) | v1_tops_2(B_56, A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_125, c_2])).
% 2.43/1.32  tff(c_447, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_437, c_133])).
% 2.43/1.32  tff(c_452, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_35, c_447])).
% 2.43/1.32  tff(c_453, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_452])).
% 2.43/1.32  tff(c_14, plain, (![A_11, B_17]: (~v3_pre_topc('#skF_1'(A_11, B_17), A_11) | v1_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.32  tff(c_456, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_453, c_14])).
% 2.43/1.32  tff(c_459, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_35, c_456])).
% 2.43/1.32  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_459])).
% 2.43/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  Inference rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Ref     : 6
% 2.43/1.32  #Sup     : 80
% 2.43/1.32  #Fact    : 0
% 2.43/1.32  #Define  : 0
% 2.43/1.32  #Split   : 5
% 2.43/1.32  #Chain   : 0
% 2.43/1.32  #Close   : 0
% 2.43/1.32  
% 2.43/1.32  Ordering : KBO
% 2.43/1.32  
% 2.43/1.32  Simplification rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Subsume      : 17
% 2.43/1.32  #Demod        : 113
% 2.43/1.32  #Tautology    : 39
% 2.43/1.32  #SimpNegUnit  : 5
% 2.43/1.32  #BackRed      : 7
% 2.43/1.32  
% 2.43/1.32  #Partial instantiations: 0
% 2.43/1.32  #Strategies tried      : 1
% 2.43/1.32  
% 2.43/1.32  Timing (in seconds)
% 2.43/1.32  ----------------------
% 2.43/1.32  Preprocessing        : 0.29
% 2.43/1.32  Parsing              : 0.16
% 2.43/1.32  CNF conversion       : 0.02
% 2.43/1.32  Main loop            : 0.27
% 2.43/1.32  Inferencing          : 0.10
% 2.43/1.32  Reduction            : 0.09
% 2.43/1.32  Demodulation         : 0.06
% 2.43/1.32  BG Simplification    : 0.02
% 2.43/1.32  Subsumption          : 0.05
% 2.43/1.32  Abstraction          : 0.01
% 2.43/1.32  MUC search           : 0.00
% 2.43/1.32  Cooper               : 0.00
% 2.43/1.32  Total                : 0.60
% 2.43/1.32  Index Insertion      : 0.00
% 2.43/1.32  Index Deletion       : 0.00
% 2.43/1.32  Index Matching       : 0.00
% 2.43/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
