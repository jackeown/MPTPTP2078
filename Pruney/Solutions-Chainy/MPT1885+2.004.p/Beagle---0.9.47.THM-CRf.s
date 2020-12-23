%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 216 expanded)
%              Number of leaves         :   25 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 (1083 expanded)
%              Number of equality atoms :   10 (  90 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v3_tex_2(C,A)
                <=> v4_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_41,plain,(
    ! [B_29,A_30] :
      ( v2_tex_2(B_29,A_30)
      | ~ v3_tex_2(B_29,A_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_47,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_44])).

tff(c_107,plain,(
    ! [A_44,B_45] :
      ( ~ v2_struct_0('#skF_2'(A_44,B_45))
      | ~ v2_tex_2(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | v1_xboole_0(B_45)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_113,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_117,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_47,c_113])).

tff(c_118,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_117])).

tff(c_83,plain,(
    ! [A_40,B_41] :
      ( v1_pre_topc('#skF_2'(A_40,B_41))
      | ~ v2_tex_2(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | v1_xboole_0(B_41)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_89,plain,
    ( v1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_83])).

tff(c_93,plain,
    ( v1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_47,c_89])).

tff(c_94,plain,(
    v1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_93])).

tff(c_121,plain,(
    ! [A_50,B_51] :
      ( m1_pre_topc('#skF_2'(A_50,B_51),A_50)
      | ~ v2_tex_2(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_125,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_121])).

tff(c_129,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_47,c_125])).

tff(c_130,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_129])).

tff(c_131,plain,(
    ! [A_52,B_53] :
      ( u1_struct_0('#skF_2'(A_52,B_53)) = B_53
      | ~ v2_tex_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(B_53)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_137,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_131])).

tff(c_141,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_47,c_137])).

tff(c_142,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_141])).

tff(c_26,plain,(
    ! [B_21,A_17] :
      ( v4_tex_2(B_21,A_17)
      | ~ v3_tex_2(u1_struct_0(B_21),A_17)
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_pre_topc(B_21,A_17)
      | ~ l1_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_157,plain,(
    ! [A_17] :
      ( v4_tex_2('#skF_2'('#skF_3','#skF_4'),A_17)
      | ~ v3_tex_2(u1_struct_0('#skF_2'('#skF_3','#skF_4')),A_17)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_4'),A_17)
      | ~ l1_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_26])).

tff(c_198,plain,(
    ! [A_57] :
      ( v4_tex_2('#skF_2'('#skF_3','#skF_4'),A_57)
      | ~ v3_tex_2('#skF_4',A_57)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_4'),A_57)
      | ~ l1_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_157])).

tff(c_204,plain,
    ( v4_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_198])).

tff(c_208,plain,
    ( v4_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_130,c_30,c_204])).

tff(c_209,plain,(
    v4_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_208])).

tff(c_28,plain,(
    ! [C_28] :
      ( u1_struct_0(C_28) != '#skF_4'
      | ~ v4_tex_2(C_28,'#skF_3')
      | ~ m1_pre_topc(C_28,'#skF_3')
      | ~ v1_pre_topc(C_28)
      | v2_struct_0(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_212,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) != '#skF_4'
    | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_209,c_28])).

tff(c_215,plain,(
    v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_130,c_142,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.33  
% 2.40/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.33  %$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.40/1.33  
% 2.40/1.33  %Foreground sorts:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Background operators:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Foreground operators:
% 2.40/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.33  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.40/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.33  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.40/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.33  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.40/1.33  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.40/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.33  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.40/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.40/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.40/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.33  
% 2.40/1.35  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 2.40/1.35  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.40/1.35  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 2.40/1.35  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v3_tex_2(C, A) <=> v4_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_tex_2)).
% 2.40/1.35  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.40/1.35  tff(c_34, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.40/1.35  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.40/1.35  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.40/1.35  tff(c_30, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.40/1.35  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.40/1.35  tff(c_41, plain, (![B_29, A_30]: (v2_tex_2(B_29, A_30) | ~v3_tex_2(B_29, A_30) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.40/1.35  tff(c_44, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_41])).
% 2.40/1.35  tff(c_47, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_44])).
% 2.40/1.35  tff(c_107, plain, (![A_44, B_45]: (~v2_struct_0('#skF_2'(A_44, B_45)) | ~v2_tex_2(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | v1_xboole_0(B_45) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.40/1.35  tff(c_113, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_107])).
% 2.40/1.35  tff(c_117, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_47, c_113])).
% 2.40/1.35  tff(c_118, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_117])).
% 2.40/1.35  tff(c_83, plain, (![A_40, B_41]: (v1_pre_topc('#skF_2'(A_40, B_41)) | ~v2_tex_2(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | v1_xboole_0(B_41) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.40/1.35  tff(c_89, plain, (v1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_83])).
% 2.40/1.35  tff(c_93, plain, (v1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_47, c_89])).
% 2.40/1.35  tff(c_94, plain, (v1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_93])).
% 2.40/1.35  tff(c_121, plain, (![A_50, B_51]: (m1_pre_topc('#skF_2'(A_50, B_51), A_50) | ~v2_tex_2(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.40/1.35  tff(c_125, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_121])).
% 2.40/1.35  tff(c_129, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_47, c_125])).
% 2.40/1.35  tff(c_130, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_129])).
% 2.40/1.35  tff(c_131, plain, (![A_52, B_53]: (u1_struct_0('#skF_2'(A_52, B_53))=B_53 | ~v2_tex_2(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(B_53) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.40/1.35  tff(c_137, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_131])).
% 2.40/1.35  tff(c_141, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_47, c_137])).
% 2.40/1.35  tff(c_142, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_141])).
% 2.40/1.35  tff(c_26, plain, (![B_21, A_17]: (v4_tex_2(B_21, A_17) | ~v3_tex_2(u1_struct_0(B_21), A_17) | ~m1_subset_1(u1_struct_0(B_21), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_pre_topc(B_21, A_17) | ~l1_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.35  tff(c_157, plain, (![A_17]: (v4_tex_2('#skF_2'('#skF_3', '#skF_4'), A_17) | ~v3_tex_2(u1_struct_0('#skF_2'('#skF_3', '#skF_4')), A_17) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), A_17) | ~l1_pre_topc(A_17) | v2_struct_0(A_17))), inference(superposition, [status(thm), theory('equality')], [c_142, c_26])).
% 2.40/1.35  tff(c_198, plain, (![A_57]: (v4_tex_2('#skF_2'('#skF_3', '#skF_4'), A_57) | ~v3_tex_2('#skF_4', A_57) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), A_57) | ~l1_pre_topc(A_57) | v2_struct_0(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_157])).
% 2.40/1.35  tff(c_204, plain, (v4_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_198])).
% 2.40/1.35  tff(c_208, plain, (v4_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_130, c_30, c_204])).
% 2.40/1.35  tff(c_209, plain, (v4_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_208])).
% 2.40/1.35  tff(c_28, plain, (![C_28]: (u1_struct_0(C_28)!='#skF_4' | ~v4_tex_2(C_28, '#skF_3') | ~m1_pre_topc(C_28, '#skF_3') | ~v1_pre_topc(C_28) | v2_struct_0(C_28))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.40/1.35  tff(c_212, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))!='#skF_4' | ~m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_209, c_28])).
% 2.40/1.35  tff(c_215, plain, (v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_130, c_142, c_212])).
% 2.40/1.35  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_215])).
% 2.40/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.35  
% 2.40/1.35  Inference rules
% 2.40/1.35  ----------------------
% 2.40/1.35  #Ref     : 0
% 2.40/1.35  #Sup     : 37
% 2.40/1.35  #Fact    : 0
% 2.40/1.35  #Define  : 0
% 2.40/1.35  #Split   : 1
% 2.40/1.35  #Chain   : 0
% 2.40/1.35  #Close   : 0
% 2.40/1.35  
% 2.40/1.35  Ordering : KBO
% 2.40/1.35  
% 2.40/1.35  Simplification rules
% 2.40/1.35  ----------------------
% 2.40/1.35  #Subsume      : 2
% 2.40/1.35  #Demod        : 35
% 2.40/1.35  #Tautology    : 5
% 2.40/1.35  #SimpNegUnit  : 15
% 2.40/1.35  #BackRed      : 0
% 2.40/1.35  
% 2.40/1.35  #Partial instantiations: 0
% 2.40/1.35  #Strategies tried      : 1
% 2.40/1.35  
% 2.40/1.35  Timing (in seconds)
% 2.40/1.35  ----------------------
% 2.40/1.35  Preprocessing        : 0.32
% 2.40/1.35  Parsing              : 0.18
% 2.40/1.35  CNF conversion       : 0.02
% 2.40/1.35  Main loop            : 0.23
% 2.40/1.35  Inferencing          : 0.08
% 2.40/1.35  Reduction            : 0.07
% 2.40/1.35  Demodulation         : 0.05
% 2.40/1.35  BG Simplification    : 0.02
% 2.40/1.35  Subsumption          : 0.05
% 2.40/1.35  Abstraction          : 0.01
% 2.40/1.35  MUC search           : 0.00
% 2.40/1.35  Cooper               : 0.00
% 2.40/1.35  Total                : 0.58
% 2.40/1.35  Index Insertion      : 0.00
% 2.40/1.35  Index Deletion       : 0.00
% 2.40/1.35  Index Matching       : 0.00
% 2.40/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
