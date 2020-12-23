%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:56 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 325 expanded)
%              Number of leaves         :   21 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          :  126 (1059 expanded)
%              Number of equality atoms :   25 ( 196 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1('#skF_1'(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | v1_tex_2(B_31,A_30)
      | ~ m1_pre_topc(B_31,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [B_20,A_19] :
      ( v1_subset_1(B_20,A_19)
      | B_20 = A_19
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    ! [A_34,B_35] :
      ( v1_subset_1('#skF_1'(A_34,B_35),u1_struct_0(A_34))
      | u1_struct_0(A_34) = '#skF_1'(A_34,B_35)
      | v1_tex_2(B_35,A_34)
      | ~ m1_pre_topc(B_35,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_46,c_14])).

tff(c_8,plain,(
    ! [A_9,B_15] :
      ( ~ v1_subset_1('#skF_1'(A_9,B_15),u1_struct_0(A_9))
      | v1_tex_2(B_15,A_9)
      | ~ m1_pre_topc(B_15,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [A_36,B_37] :
      ( u1_struct_0(A_36) = '#skF_1'(A_36,B_37)
      | v1_tex_2(B_37,A_36)
      | ~ m1_pre_topc(B_37,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_64,c_8])).

tff(c_22,plain,(
    ~ v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76,plain,
    ( u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_22])).

tff(c_79,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_76])).

tff(c_30,plain,(
    ! [B_26,A_27] :
      ( u1_struct_0(B_26) = '#skF_1'(A_27,B_26)
      | v1_tex_2(B_26,A_27)
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_33,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_22])).

tff(c_36,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_33])).

tff(c_18,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_37,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_80,plain,(
    g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) != g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_37])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_pre_topc(A_1,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_9,B_15] :
      ( m1_subset_1('#skF_1'(A_9,B_15),k1_zfmisc_1(u1_struct_0(A_9)))
      | v1_tex_2(B_15,A_9)
      | ~ m1_pre_topc(B_15,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [B_15] :
      ( m1_subset_1('#skF_1'('#skF_2',B_15),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
      | v1_tex_2(B_15,'#skF_2')
      | ~ m1_pre_topc(B_15,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_12])).

tff(c_105,plain,(
    ! [B_39] :
      ( m1_subset_1('#skF_1'('#skF_2',B_39),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
      | v1_tex_2(B_39,'#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_16,plain,(
    ! [B_20] :
      ( ~ v1_subset_1(B_20,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3'))
    | v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_16])).

tff(c_116,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3'))
    | v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_112])).

tff(c_117,plain,(
    ~ v1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_116])).

tff(c_6,plain,(
    ! [B_15,A_9] :
      ( v1_subset_1(u1_struct_0(B_15),u1_struct_0(A_9))
      | ~ m1_subset_1(u1_struct_0(B_15),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ v1_tex_2(B_15,A_9)
      | ~ m1_pre_topc(B_15,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_87,plain,(
    ! [B_15] :
      ( v1_subset_1(u1_struct_0(B_15),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_15),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
      | ~ v1_tex_2(B_15,'#skF_2')
      | ~ m1_pre_topc(B_15,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_6])).

tff(c_118,plain,(
    ! [B_40] :
      ( v1_subset_1(u1_struct_0(B_40),'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_40),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
      | ~ v1_tex_2(B_40,'#skF_2')
      | ~ m1_pre_topc(B_40,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_79,c_87])).

tff(c_121,plain,
    ( v1_subset_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
    | ~ v1_tex_2('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_118])).

tff(c_125,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
    | ~ v1_tex_2('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_121])).

tff(c_126,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
    | ~ v1_tex_2('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_125])).

tff(c_139,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_142,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_139])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_142])).

tff(c_148,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_130,plain,(
    ! [C_41,B_42,A_43] :
      ( g1_pre_topc(u1_struct_0(C_41),u1_pre_topc(C_41)) = g1_pre_topc(u1_struct_0(B_42),u1_pre_topc(B_42))
      | u1_struct_0(C_41) != u1_struct_0(B_42)
      | ~ m1_pre_topc(C_41,A_43)
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,(
    ! [B_42] :
      ( g1_pre_topc(u1_struct_0(B_42),u1_pre_topc(B_42)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_42) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_42,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_130])).

tff(c_154,plain,(
    ! [B_44] :
      ( g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) = g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_44) != '#skF_1'('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_44,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36,c_36,c_134])).

tff(c_163,plain,
    ( g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))
    | u1_struct_0('#skF_2') != '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_154])).

tff(c_170,plain,(
    g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_79,c_163])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:15:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.27  
% 2.01/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.27  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.27  
% 2.01/1.27  %Foreground sorts:
% 2.01/1.27  
% 2.01/1.27  
% 2.01/1.27  %Background operators:
% 2.01/1.27  
% 2.01/1.27  
% 2.01/1.27  %Foreground operators:
% 2.01/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.01/1.27  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.27  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.01/1.27  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.01/1.27  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.01/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.01/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.01/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.01/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.27  
% 2.01/1.29  tff(f_76, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_tex_2(B, A) & m1_pre_topc(B, A)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tex_2)).
% 2.01/1.29  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.01/1.29  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.01/1.29  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.01/1.29  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => ((u1_struct_0(B) = u1_struct_0(C)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tsep_1)).
% 2.01/1.29  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_46, plain, (![A_30, B_31]: (m1_subset_1('#skF_1'(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | v1_tex_2(B_31, A_30) | ~m1_pre_topc(B_31, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.29  tff(c_14, plain, (![B_20, A_19]: (v1_subset_1(B_20, A_19) | B_20=A_19 | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.01/1.29  tff(c_64, plain, (![A_34, B_35]: (v1_subset_1('#skF_1'(A_34, B_35), u1_struct_0(A_34)) | u1_struct_0(A_34)='#skF_1'(A_34, B_35) | v1_tex_2(B_35, A_34) | ~m1_pre_topc(B_35, A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_46, c_14])).
% 2.01/1.29  tff(c_8, plain, (![A_9, B_15]: (~v1_subset_1('#skF_1'(A_9, B_15), u1_struct_0(A_9)) | v1_tex_2(B_15, A_9) | ~m1_pre_topc(B_15, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.29  tff(c_73, plain, (![A_36, B_37]: (u1_struct_0(A_36)='#skF_1'(A_36, B_37) | v1_tex_2(B_37, A_36) | ~m1_pre_topc(B_37, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_64, c_8])).
% 2.01/1.29  tff(c_22, plain, (~v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_76, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_73, c_22])).
% 2.01/1.29  tff(c_79, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_76])).
% 2.01/1.29  tff(c_30, plain, (![B_26, A_27]: (u1_struct_0(B_26)='#skF_1'(A_27, B_26) | v1_tex_2(B_26, A_27) | ~m1_pre_topc(B_26, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.29  tff(c_33, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_22])).
% 2.01/1.29  tff(c_36, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_33])).
% 2.01/1.29  tff(c_18, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_37, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 2.01/1.29  tff(c_80, plain, (g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))!=g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_37])).
% 2.01/1.29  tff(c_2, plain, (![A_1]: (m1_pre_topc(A_1, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.29  tff(c_12, plain, (![A_9, B_15]: (m1_subset_1('#skF_1'(A_9, B_15), k1_zfmisc_1(u1_struct_0(A_9))) | v1_tex_2(B_15, A_9) | ~m1_pre_topc(B_15, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.29  tff(c_90, plain, (![B_15]: (m1_subset_1('#skF_1'('#skF_2', B_15), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | v1_tex_2(B_15, '#skF_2') | ~m1_pre_topc(B_15, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_12])).
% 2.01/1.29  tff(c_105, plain, (![B_39]: (m1_subset_1('#skF_1'('#skF_2', B_39), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | v1_tex_2(B_39, '#skF_2') | ~m1_pre_topc(B_39, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_90])).
% 2.01/1.29  tff(c_16, plain, (![B_20]: (~v1_subset_1(B_20, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.01/1.29  tff(c_112, plain, (~v1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3')) | v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_105, c_16])).
% 2.01/1.29  tff(c_116, plain, (~v1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3')) | v1_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_112])).
% 2.01/1.29  tff(c_117, plain, (~v1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_22, c_116])).
% 2.01/1.29  tff(c_6, plain, (![B_15, A_9]: (v1_subset_1(u1_struct_0(B_15), u1_struct_0(A_9)) | ~m1_subset_1(u1_struct_0(B_15), k1_zfmisc_1(u1_struct_0(A_9))) | ~v1_tex_2(B_15, A_9) | ~m1_pre_topc(B_15, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.29  tff(c_87, plain, (![B_15]: (v1_subset_1(u1_struct_0(B_15), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0(B_15), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~v1_tex_2(B_15, '#skF_2') | ~m1_pre_topc(B_15, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_6])).
% 2.01/1.29  tff(c_118, plain, (![B_40]: (v1_subset_1(u1_struct_0(B_40), '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(u1_struct_0(B_40), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~v1_tex_2(B_40, '#skF_2') | ~m1_pre_topc(B_40, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_79, c_87])).
% 2.01/1.29  tff(c_121, plain, (v1_subset_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~v1_tex_2('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_118])).
% 2.01/1.29  tff(c_125, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~v1_tex_2('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_121])).
% 2.01/1.29  tff(c_126, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~v1_tex_2('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_117, c_125])).
% 2.01/1.29  tff(c_139, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 2.01/1.29  tff(c_142, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_139])).
% 2.01/1.29  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_142])).
% 2.01/1.29  tff(c_148, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 2.01/1.29  tff(c_130, plain, (![C_41, B_42, A_43]: (g1_pre_topc(u1_struct_0(C_41), u1_pre_topc(C_41))=g1_pre_topc(u1_struct_0(B_42), u1_pre_topc(B_42)) | u1_struct_0(C_41)!=u1_struct_0(B_42) | ~m1_pre_topc(C_41, A_43) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.29  tff(c_134, plain, (![B_42]: (g1_pre_topc(u1_struct_0(B_42), u1_pre_topc(B_42))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | u1_struct_0(B_42)!=u1_struct_0('#skF_3') | ~m1_pre_topc(B_42, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_130])).
% 2.01/1.29  tff(c_154, plain, (![B_44]: (g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))=g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')) | u1_struct_0(B_44)!='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc(B_44, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36, c_36, c_134])).
% 2.01/1.29  tff(c_163, plain, (g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))=g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')) | u1_struct_0('#skF_2')!='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79, c_154])).
% 2.01/1.29  tff(c_170, plain, (g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))=g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_79, c_163])).
% 2.01/1.29  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_170])).
% 2.01/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  Inference rules
% 2.01/1.29  ----------------------
% 2.01/1.29  #Ref     : 0
% 2.01/1.29  #Sup     : 29
% 2.01/1.29  #Fact    : 0
% 2.01/1.29  #Define  : 0
% 2.01/1.29  #Split   : 2
% 2.01/1.29  #Chain   : 0
% 2.01/1.29  #Close   : 0
% 2.01/1.29  
% 2.01/1.29  Ordering : KBO
% 2.01/1.29  
% 2.01/1.29  Simplification rules
% 2.01/1.29  ----------------------
% 2.01/1.29  #Subsume      : 5
% 2.01/1.29  #Demod        : 27
% 2.01/1.29  #Tautology    : 6
% 2.01/1.29  #SimpNegUnit  : 4
% 2.01/1.29  #BackRed      : 2
% 2.01/1.29  
% 2.01/1.29  #Partial instantiations: 0
% 2.01/1.29  #Strategies tried      : 1
% 2.01/1.29  
% 2.01/1.29  Timing (in seconds)
% 2.01/1.29  ----------------------
% 2.01/1.29  Preprocessing        : 0.31
% 2.01/1.29  Parsing              : 0.16
% 2.01/1.29  CNF conversion       : 0.02
% 2.01/1.29  Main loop            : 0.17
% 2.01/1.29  Inferencing          : 0.06
% 2.01/1.29  Reduction            : 0.05
% 2.01/1.29  Demodulation         : 0.03
% 2.01/1.29  BG Simplification    : 0.01
% 2.01/1.29  Subsumption          : 0.04
% 2.01/1.29  Abstraction          : 0.01
% 2.01/1.29  MUC search           : 0.00
% 2.01/1.29  Cooper               : 0.00
% 2.01/1.29  Total                : 0.51
% 2.01/1.29  Index Insertion      : 0.00
% 2.01/1.29  Index Deletion       : 0.00
% 2.01/1.29  Index Matching       : 0.00
% 2.01/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
