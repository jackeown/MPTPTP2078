%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:11 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 170 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 567 expanded)
%              Number of equality atoms :    5 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_102,negated_conjecture,(
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
                        & v2_tops_2(C,A) )
                     => v2_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_26,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    ~ v2_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    ~ v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_148,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),B_69)
      | v2_tops_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68))))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_150,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v2_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_148])).

tff(c_155,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_150])).

tff(c_156,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_155])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_206,plain,(
    ! [C_81,A_82,B_83] :
      ( v4_pre_topc(C_81,A_82)
      | ~ r2_hidden(C_81,B_83)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v2_tops_2(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82))))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_299,plain,(
    ! [A_92] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),A_92)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v2_tops_2('#skF_4',A_92)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_92))))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_156,c_206])).

tff(c_307,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_299])).

tff(c_318,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_36,c_32,c_24,c_307])).

tff(c_20,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_7,B_9] :
      ( m1_pre_topc(A_7,g1_pre_topc(u1_struct_0(B_9),u1_pre_topc(B_9)))
      | ~ m1_pre_topc(A_7,B_9)
      | ~ l1_pre_topc(B_9)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_65,plain,(
    ! [B_57,A_58] :
      ( m1_pre_topc(B_57,A_58)
      | ~ m1_pre_topc(B_57,g1_pre_topc(u1_struct_0(A_58),u1_pre_topc(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [B_57] :
      ( m1_pre_topc(B_57,'#skF_2')
      | ~ m1_pre_topc(B_57,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_65])).

tff(c_86,plain,(
    ! [B_61] :
      ( m1_pre_topc(B_61,'#skF_2')
      | ~ m1_pre_topc(B_61,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_90,plain,(
    ! [A_7] :
      ( m1_pre_topc(A_7,'#skF_2')
      | ~ m1_pre_topc(A_7,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_97,plain,(
    ! [A_7] :
      ( m1_pre_topc(A_7,'#skF_2')
      | ~ m1_pre_topc(A_7,'#skF_3')
      | ~ l1_pre_topc(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_90])).

tff(c_53,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_37,c_48])).

tff(c_172,plain,(
    ! [D_75,C_76,A_77] :
      ( v4_pre_topc(D_75,C_76)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(C_76)))
      | ~ v4_pre_topc(D_75,A_77)
      | ~ m1_pre_topc(C_76,A_77)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_210,plain,(
    ! [A_84,A_85] :
      ( v4_pre_topc(A_84,'#skF_3')
      | ~ v4_pre_topc(A_84,A_85)
      | ~ m1_pre_topc('#skF_3',A_85)
      | ~ m1_subset_1(A_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ r2_hidden(A_84,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_53,c_172])).

tff(c_216,plain,(
    ! [A_48] :
      ( v4_pre_topc(A_48,'#skF_3')
      | ~ v4_pre_topc(A_48,'#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_223,plain,(
    ! [A_48] :
      ( v4_pre_topc(A_48,'#skF_3')
      | ~ v4_pre_topc(A_48,'#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_216])).

tff(c_227,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_230,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_227])).

tff(c_233,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_230])).

tff(c_259,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_233])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_259])).

tff(c_264,plain,(
    ! [A_48] :
      ( v4_pre_topc(A_48,'#skF_3')
      | ~ v4_pre_topc(A_48,'#skF_2')
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_324,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_318,c_264])).

tff(c_327,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_324])).

tff(c_12,plain,(
    ! [A_10,B_16] :
      ( ~ v4_pre_topc('#skF_1'(A_10,B_16),A_10)
      | v2_tops_2(B_16,A_10)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_329,plain,
    ( v2_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_327,c_12])).

tff(c_332,plain,(
    v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37,c_329])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  %$ v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.50/1.34  
% 2.50/1.34  %Foreground sorts:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Background operators:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Foreground operators:
% 2.50/1.34  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.34  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.50/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.34  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.50/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.50/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.34  
% 2.50/1.35  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tops_2(C, A)) => v2_tops_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_waybel_9)).
% 2.50/1.35  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 2.50/1.35  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.50/1.35  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.50/1.35  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.50/1.35  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 2.50/1.35  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 2.50/1.35  tff(c_26, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_22, plain, (~v2_tops_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_38, plain, (~v2_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 2.50/1.35  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_37, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.50/1.35  tff(c_148, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), B_69) | v2_tops_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68)))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.50/1.35  tff(c_150, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v2_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_37, c_148])).
% 2.50/1.35  tff(c_155, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v2_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_150])).
% 2.50/1.35  tff(c_156, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_155])).
% 2.50/1.35  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_24, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_48, plain, (![A_48, C_49, B_50]: (m1_subset_1(A_48, C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.35  tff(c_54, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.50/1.35  tff(c_206, plain, (![C_81, A_82, B_83]: (v4_pre_topc(C_81, A_82) | ~r2_hidden(C_81, B_83) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~v2_tops_2(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82)))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.50/1.35  tff(c_299, plain, (![A_92]: (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_92) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_92))) | ~v2_tops_2('#skF_4', A_92) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_92)))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_156, c_206])).
% 2.50/1.35  tff(c_307, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~v2_tops_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_54, c_299])).
% 2.50/1.35  tff(c_318, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_36, c_32, c_24, c_307])).
% 2.50/1.35  tff(c_20, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.50/1.35  tff(c_8, plain, (![A_7, B_9]: (m1_pre_topc(A_7, g1_pre_topc(u1_struct_0(B_9), u1_pre_topc(B_9))) | ~m1_pre_topc(A_7, B_9) | ~l1_pre_topc(B_9) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.35  tff(c_28, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.50/1.35  tff(c_65, plain, (![B_57, A_58]: (m1_pre_topc(B_57, A_58) | ~m1_pre_topc(B_57, g1_pre_topc(u1_struct_0(A_58), u1_pre_topc(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.35  tff(c_68, plain, (![B_57]: (m1_pre_topc(B_57, '#skF_2') | ~m1_pre_topc(B_57, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_65])).
% 2.50/1.35  tff(c_86, plain, (![B_61]: (m1_pre_topc(B_61, '#skF_2') | ~m1_pre_topc(B_61, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68])).
% 2.50/1.35  tff(c_90, plain, (![A_7]: (m1_pre_topc(A_7, '#skF_2') | ~m1_pre_topc(A_7, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_8, c_86])).
% 2.50/1.35  tff(c_97, plain, (![A_7]: (m1_pre_topc(A_7, '#skF_2') | ~m1_pre_topc(A_7, '#skF_3') | ~l1_pre_topc(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_90])).
% 2.50/1.35  tff(c_53, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_37, c_48])).
% 2.50/1.35  tff(c_172, plain, (![D_75, C_76, A_77]: (v4_pre_topc(D_75, C_76) | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0(C_76))) | ~v4_pre_topc(D_75, A_77) | ~m1_pre_topc(C_76, A_77) | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.50/1.35  tff(c_210, plain, (![A_84, A_85]: (v4_pre_topc(A_84, '#skF_3') | ~v4_pre_topc(A_84, A_85) | ~m1_pre_topc('#skF_3', A_85) | ~m1_subset_1(A_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~r2_hidden(A_84, '#skF_4'))), inference(resolution, [status(thm)], [c_53, c_172])).
% 2.50/1.35  tff(c_216, plain, (![A_48]: (v4_pre_topc(A_48, '#skF_3') | ~v4_pre_topc(A_48, '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_210])).
% 2.50/1.35  tff(c_223, plain, (![A_48]: (v4_pre_topc(A_48, '#skF_3') | ~v4_pre_topc(A_48, '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~r2_hidden(A_48, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_216])).
% 2.50/1.35  tff(c_227, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_223])).
% 2.50/1.35  tff(c_230, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_97, c_227])).
% 2.50/1.35  tff(c_233, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_230])).
% 2.50/1.35  tff(c_259, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_233])).
% 2.50/1.35  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_259])).
% 2.50/1.35  tff(c_264, plain, (![A_48]: (v4_pre_topc(A_48, '#skF_3') | ~v4_pre_topc(A_48, '#skF_2') | ~r2_hidden(A_48, '#skF_4'))), inference(splitRight, [status(thm)], [c_223])).
% 2.50/1.35  tff(c_324, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_318, c_264])).
% 2.50/1.35  tff(c_327, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_324])).
% 2.50/1.35  tff(c_12, plain, (![A_10, B_16]: (~v4_pre_topc('#skF_1'(A_10, B_16), A_10) | v2_tops_2(B_16, A_10) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.50/1.35  tff(c_329, plain, (v2_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_327, c_12])).
% 2.50/1.35  tff(c_332, plain, (v2_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_37, c_329])).
% 2.50/1.35  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_332])).
% 2.50/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  Inference rules
% 2.50/1.35  ----------------------
% 2.50/1.35  #Ref     : 0
% 2.50/1.35  #Sup     : 54
% 2.50/1.35  #Fact    : 0
% 2.50/1.35  #Define  : 0
% 2.50/1.35  #Split   : 3
% 2.50/1.35  #Chain   : 0
% 2.50/1.35  #Close   : 0
% 2.50/1.35  
% 2.50/1.35  Ordering : KBO
% 2.50/1.35  
% 2.50/1.35  Simplification rules
% 2.50/1.35  ----------------------
% 2.50/1.35  #Subsume      : 12
% 2.50/1.35  #Demod        : 48
% 2.50/1.35  #Tautology    : 12
% 2.50/1.35  #SimpNegUnit  : 4
% 2.50/1.35  #BackRed      : 0
% 2.50/1.35  
% 2.50/1.35  #Partial instantiations: 0
% 2.50/1.35  #Strategies tried      : 1
% 2.50/1.35  
% 2.50/1.35  Timing (in seconds)
% 2.50/1.35  ----------------------
% 2.50/1.36  Preprocessing        : 0.31
% 2.50/1.36  Parsing              : 0.17
% 2.50/1.36  CNF conversion       : 0.02
% 2.50/1.36  Main loop            : 0.24
% 2.50/1.36  Inferencing          : 0.09
% 2.50/1.36  Reduction            : 0.07
% 2.50/1.36  Demodulation         : 0.05
% 2.50/1.36  BG Simplification    : 0.01
% 2.50/1.36  Subsumption          : 0.05
% 2.50/1.36  Abstraction          : 0.01
% 2.50/1.36  MUC search           : 0.00
% 2.50/1.36  Cooper               : 0.00
% 2.50/1.36  Total                : 0.59
% 2.50/1.36  Index Insertion      : 0.00
% 2.50/1.36  Index Deletion       : 0.00
% 2.50/1.36  Index Matching       : 0.00
% 2.50/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
