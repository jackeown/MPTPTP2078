%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:49 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 150 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 475 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_72,plain,(
    ! [A_35,B_36] :
      ( v1_pre_topc('#skF_1'(A_35,B_36))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | v1_xboole_0(B_36)
      | ~ l1_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,
    ( v1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_82,plain,
    ( v1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75])).

tff(c_83,plain,
    ( v1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82])).

tff(c_85,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_159,plain,(
    ! [B_44,A_45] :
      ( v2_tex_2(B_44,A_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ v1_xboole_0(B_44)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_165,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_172,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_85,c_165])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_24,c_172])).

tff(c_176,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_327,plain,(
    ! [A_55,B_56] :
      ( m1_pre_topc('#skF_1'(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | v1_xboole_0(B_56)
      | ~ l1_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_333,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_327])).

tff(c_340,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_333])).

tff(c_341,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_176,c_340])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_16,plain,(
    ! [A_12] :
      ( v2_tex_2(u1_struct_0(A_12),A_12)
      | ~ v1_tdlat_3(A_12)
      | ~ m1_subset_1(u1_struct_0(A_12),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37,plain,(
    ! [A_12] :
      ( v2_tex_2(u1_struct_0(A_12),A_12)
      | ~ v1_tdlat_3(A_12)
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_16])).

tff(c_177,plain,(
    ! [A_46,B_47] :
      ( u1_struct_0('#skF_1'(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | v1_xboole_0(B_47)
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_180,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_177])).

tff(c_187,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_180])).

tff(c_188,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_176,c_187])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( r1_tarski(u1_struct_0(B_5),u1_struct_0(A_3))
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_352,plain,(
    ! [C_58,A_59,B_60] :
      ( v2_tex_2(C_58,A_59)
      | ~ v2_tex_2(B_60,A_59)
      | ~ r1_tarski(C_58,B_60)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_409,plain,(
    ! [B_67,A_68,A_69] :
      ( v2_tex_2(u1_struct_0(B_67),A_68)
      | ~ v2_tex_2(u1_struct_0(A_69),A_68)
      | ~ m1_subset_1(u1_struct_0(B_67),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(u1_struct_0(A_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ m1_pre_topc(B_67,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_6,c_352])).

tff(c_415,plain,(
    ! [A_68,A_69] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_68)
      | ~ v2_tex_2(u1_struct_0(A_69),A_68)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(u1_struct_0(A_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_409])).

tff(c_439,plain,(
    ! [A_72,A_73] :
      ( v2_tex_2('#skF_3',A_72)
      | ~ v2_tex_2(u1_struct_0(A_73),A_72)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(u1_struct_0(A_73),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_415])).

tff(c_460,plain,(
    ! [A_74] :
      ( v2_tex_2('#skF_3',A_74)
      | ~ v2_tex_2(u1_struct_0(A_74),A_74)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_35,c_439])).

tff(c_490,plain,(
    ! [A_76] :
      ( v2_tex_2('#skF_3',A_76)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_76)
      | ~ v1_tdlat_3(A_76)
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_37,c_460])).

tff(c_499,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_490])).

tff(c_505,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_341,c_499])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_24,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:33:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  %$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.38  
% 2.65/1.38  %Foreground sorts:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Background operators:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Foreground operators:
% 2.65/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.38  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.65/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.65/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.38  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.65/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.65/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.65/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.38  
% 2.65/1.39  tff(f_114, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.65/1.39  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 2.65/1.39  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.65/1.39  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.65/1.39  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.65/1.39  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.65/1.39  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 2.65/1.39  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 2.65/1.39  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.65/1.39  tff(c_24, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.65/1.39  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.65/1.39  tff(c_30, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.65/1.39  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.65/1.39  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.65/1.39  tff(c_72, plain, (![A_35, B_36]: (v1_pre_topc('#skF_1'(A_35, B_36)) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | v1_xboole_0(B_36) | ~l1_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.39  tff(c_75, plain, (v1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_72])).
% 2.65/1.39  tff(c_82, plain, (v1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_75])).
% 2.65/1.39  tff(c_83, plain, (v1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_82])).
% 2.65/1.39  tff(c_85, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_83])).
% 2.65/1.39  tff(c_159, plain, (![B_44, A_45]: (v2_tex_2(B_44, A_45) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~v1_xboole_0(B_44) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.39  tff(c_165, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_159])).
% 2.65/1.39  tff(c_172, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_85, c_165])).
% 2.65/1.39  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_24, c_172])).
% 2.65/1.39  tff(c_176, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_83])).
% 2.65/1.39  tff(c_327, plain, (![A_55, B_56]: (m1_pre_topc('#skF_1'(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | v1_xboole_0(B_56) | ~l1_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.39  tff(c_333, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_327])).
% 2.65/1.39  tff(c_340, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_333])).
% 2.65/1.39  tff(c_341, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_176, c_340])).
% 2.65/1.39  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.39  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.39  tff(c_35, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.65/1.39  tff(c_16, plain, (![A_12]: (v2_tex_2(u1_struct_0(A_12), A_12) | ~v1_tdlat_3(A_12) | ~m1_subset_1(u1_struct_0(A_12), k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.39  tff(c_37, plain, (![A_12]: (v2_tex_2(u1_struct_0(A_12), A_12) | ~v1_tdlat_3(A_12) | ~l1_pre_topc(A_12) | v2_struct_0(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_16])).
% 2.65/1.39  tff(c_177, plain, (![A_46, B_47]: (u1_struct_0('#skF_1'(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | v1_xboole_0(B_47) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.39  tff(c_180, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_177])).
% 2.65/1.39  tff(c_187, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_180])).
% 2.65/1.39  tff(c_188, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_34, c_176, c_187])).
% 2.65/1.39  tff(c_6, plain, (![B_5, A_3]: (r1_tarski(u1_struct_0(B_5), u1_struct_0(A_3)) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.65/1.39  tff(c_352, plain, (![C_58, A_59, B_60]: (v2_tex_2(C_58, A_59) | ~v2_tex_2(B_60, A_59) | ~r1_tarski(C_58, B_60) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.39  tff(c_409, plain, (![B_67, A_68, A_69]: (v2_tex_2(u1_struct_0(B_67), A_68) | ~v2_tex_2(u1_struct_0(A_69), A_68) | ~m1_subset_1(u1_struct_0(B_67), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(u1_struct_0(A_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~m1_pre_topc(B_67, A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_6, c_352])).
% 2.65/1.39  tff(c_415, plain, (![A_68, A_69]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_68) | ~v2_tex_2(u1_struct_0(A_69), A_68) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(u1_struct_0(A_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_69) | ~l1_pre_topc(A_69))), inference(superposition, [status(thm), theory('equality')], [c_188, c_409])).
% 2.65/1.39  tff(c_439, plain, (![A_72, A_73]: (v2_tex_2('#skF_3', A_72) | ~v2_tex_2(u1_struct_0(A_73), A_72) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(u1_struct_0(A_73), k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_73) | ~l1_pre_topc(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_415])).
% 2.65/1.39  tff(c_460, plain, (![A_74]: (v2_tex_2('#skF_3', A_74) | ~v2_tex_2(u1_struct_0(A_74), A_74) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_35, c_439])).
% 2.65/1.39  tff(c_490, plain, (![A_76]: (v2_tex_2('#skF_3', A_76) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_76) | ~v1_tdlat_3(A_76) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_37, c_460])).
% 2.65/1.39  tff(c_499, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_490])).
% 2.65/1.39  tff(c_505, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_341, c_499])).
% 2.65/1.39  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_24, c_505])).
% 2.65/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  
% 2.65/1.39  Inference rules
% 2.65/1.39  ----------------------
% 2.65/1.39  #Ref     : 0
% 2.65/1.39  #Sup     : 114
% 2.65/1.39  #Fact    : 0
% 2.65/1.39  #Define  : 0
% 2.65/1.39  #Split   : 3
% 2.65/1.39  #Chain   : 0
% 2.65/1.39  #Close   : 0
% 2.65/1.39  
% 2.65/1.39  Ordering : KBO
% 2.65/1.39  
% 2.65/1.39  Simplification rules
% 2.65/1.39  ----------------------
% 2.65/1.39  #Subsume      : 29
% 2.65/1.39  #Demod        : 57
% 2.65/1.39  #Tautology    : 14
% 2.65/1.39  #SimpNegUnit  : 30
% 2.65/1.39  #BackRed      : 0
% 2.65/1.39  
% 2.65/1.39  #Partial instantiations: 0
% 2.65/1.39  #Strategies tried      : 1
% 2.65/1.39  
% 2.65/1.39  Timing (in seconds)
% 2.65/1.39  ----------------------
% 2.65/1.40  Preprocessing        : 0.28
% 2.65/1.40  Parsing              : 0.15
% 2.65/1.40  CNF conversion       : 0.02
% 2.65/1.40  Main loop            : 0.32
% 2.65/1.40  Inferencing          : 0.11
% 2.65/1.40  Reduction            : 0.10
% 2.65/1.40  Demodulation         : 0.07
% 2.65/1.40  BG Simplification    : 0.02
% 2.65/1.40  Subsumption          : 0.07
% 2.65/1.40  Abstraction          : 0.01
% 2.65/1.40  MUC search           : 0.00
% 2.65/1.40  Cooper               : 0.00
% 2.65/1.40  Total                : 0.63
% 2.65/1.40  Index Insertion      : 0.00
% 2.65/1.40  Index Deletion       : 0.00
% 2.65/1.40  Index Matching       : 0.00
% 2.65/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
