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
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 129 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 364 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => ( C = D
                        | r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),D))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ v1_xboole_0(C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_3,A_49] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_49,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_62,plain,(
    ! [A_49] : ~ r2_hidden(A_49,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_72,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_2'(A_56,B_57),B_57)
      | v2_tex_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_2'(A_56,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_82,plain,(
    ! [A_56] :
      ( v2_tex_2(k1_xboole_0,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_78])).

tff(c_139,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_4'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v3_tdlat_3(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [B_42] :
      ( ~ v3_tex_2(B_42,'#skF_5')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_158,plain,(
    ! [B_79] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_79),'#skF_5')
      | ~ v2_tex_2(B_79,'#skF_5')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_139,c_32])).

tff(c_168,plain,(
    ! [B_79] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_79),'#skF_5')
      | ~ v2_tex_2(B_79,'#skF_5')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_158])).

tff(c_170,plain,(
    ! [B_80] :
      ( ~ v3_tex_2('#skF_4'('#skF_5',B_80),'#skF_5')
      | ~ v2_tex_2(B_80,'#skF_5')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_168])).

tff(c_188,plain,
    ( ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5')
    | ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_189,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_192,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_189])).

tff(c_195,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_192])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_195])).

tff(c_199,plain,(
    v2_tex_2(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_95,plain,(
    ! [A_63,B_64] :
      ( v3_tex_2('#skF_4'(A_63,B_64),A_63)
      | ~ v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v3_tdlat_3(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_103,plain,(
    ! [A_63] :
      ( v3_tex_2('#skF_4'(A_63,k1_xboole_0),A_63)
      | ~ v2_tex_2(k1_xboole_0,A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v3_tdlat_3(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_198,plain,(
    ~ v3_tex_2('#skF_4'('#skF_5',k1_xboole_0),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_202,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_198])).

tff(c_205,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_199,c_202])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_205])).

tff(c_208,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_2,plain,(
    ! [A_1] : v1_xboole_0('#skF_1'(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.39  
% 2.53/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.40  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.53/1.40  
% 2.53/1.40  %Foreground sorts:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Background operators:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Foreground operators:
% 2.53/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.53/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.53/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.40  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.53/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.53/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.40  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.53/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.53/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.40  
% 2.53/1.41  tff(f_111, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.53/1.41  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.53/1.41  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.53/1.41  tff(f_73, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 2.53/1.41  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.53/1.41  tff(f_30, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.53/1.41  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.41  tff(c_38, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.41  tff(c_36, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.41  tff(c_34, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.41  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.41  tff(c_55, plain, (![C_47, B_48, A_49]: (~v1_xboole_0(C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.41  tff(c_61, plain, (![A_3, A_49]: (~v1_xboole_0(A_3) | ~r2_hidden(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_55])).
% 2.53/1.41  tff(c_62, plain, (![A_49]: (~r2_hidden(A_49, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_61])).
% 2.53/1.41  tff(c_72, plain, (![A_56, B_57]: (r2_hidden('#skF_2'(A_56, B_57), B_57) | v2_tex_2(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.41  tff(c_78, plain, (![A_56]: (r2_hidden('#skF_2'(A_56, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_56) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_6, c_72])).
% 2.53/1.41  tff(c_82, plain, (![A_56]: (v2_tex_2(k1_xboole_0, A_56) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(negUnitSimplification, [status(thm)], [c_62, c_78])).
% 2.53/1.41  tff(c_139, plain, (![A_78, B_79]: (m1_subset_1('#skF_4'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v3_tdlat_3(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.53/1.41  tff(c_32, plain, (![B_42]: (~v3_tex_2(B_42, '#skF_5') | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.41  tff(c_158, plain, (![B_79]: (~v3_tex_2('#skF_4'('#skF_5', B_79), '#skF_5') | ~v2_tex_2(B_79, '#skF_5') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_139, c_32])).
% 2.53/1.41  tff(c_168, plain, (![B_79]: (~v3_tex_2('#skF_4'('#skF_5', B_79), '#skF_5') | ~v2_tex_2(B_79, '#skF_5') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_158])).
% 2.53/1.41  tff(c_170, plain, (![B_80]: (~v3_tex_2('#skF_4'('#skF_5', B_80), '#skF_5') | ~v2_tex_2(B_80, '#skF_5') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_168])).
% 2.53/1.41  tff(c_188, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5') | ~v2_tex_2(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_6, c_170])).
% 2.53/1.41  tff(c_189, plain, (~v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_188])).
% 2.53/1.41  tff(c_192, plain, (~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_82, c_189])).
% 2.53/1.41  tff(c_195, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_192])).
% 2.53/1.41  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_195])).
% 2.53/1.41  tff(c_199, plain, (v2_tex_2(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_188])).
% 2.53/1.41  tff(c_95, plain, (![A_63, B_64]: (v3_tex_2('#skF_4'(A_63, B_64), A_63) | ~v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v3_tdlat_3(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.53/1.41  tff(c_103, plain, (![A_63]: (v3_tex_2('#skF_4'(A_63, k1_xboole_0), A_63) | ~v2_tex_2(k1_xboole_0, A_63) | ~l1_pre_topc(A_63) | ~v3_tdlat_3(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_6, c_95])).
% 2.53/1.41  tff(c_198, plain, (~v3_tex_2('#skF_4'('#skF_5', k1_xboole_0), '#skF_5')), inference(splitRight, [status(thm)], [c_188])).
% 2.53/1.41  tff(c_202, plain, (~v2_tex_2(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_103, c_198])).
% 2.53/1.41  tff(c_205, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_199, c_202])).
% 2.53/1.41  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_205])).
% 2.53/1.41  tff(c_208, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_61])).
% 2.53/1.41  tff(c_2, plain, (![A_1]: (v1_xboole_0('#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.53/1.41  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_2])).
% 2.53/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.41  
% 2.53/1.41  Inference rules
% 2.53/1.41  ----------------------
% 2.53/1.41  #Ref     : 0
% 2.53/1.41  #Sup     : 33
% 2.53/1.41  #Fact    : 0
% 2.53/1.41  #Define  : 0
% 2.53/1.41  #Split   : 2
% 2.53/1.41  #Chain   : 0
% 2.53/1.41  #Close   : 0
% 2.53/1.41  
% 2.53/1.41  Ordering : KBO
% 2.53/1.41  
% 2.53/1.41  Simplification rules
% 2.53/1.41  ----------------------
% 2.53/1.41  #Subsume      : 4
% 2.53/1.41  #Demod        : 13
% 2.53/1.41  #Tautology    : 0
% 2.53/1.41  #SimpNegUnit  : 7
% 2.53/1.41  #BackRed      : 1
% 2.53/1.41  
% 2.53/1.41  #Partial instantiations: 0
% 2.53/1.41  #Strategies tried      : 1
% 2.53/1.41  
% 2.53/1.41  Timing (in seconds)
% 2.53/1.41  ----------------------
% 2.53/1.41  Preprocessing        : 0.36
% 2.53/1.41  Parsing              : 0.19
% 2.53/1.41  CNF conversion       : 0.03
% 2.53/1.41  Main loop            : 0.20
% 2.53/1.41  Inferencing          : 0.08
% 2.53/1.42  Reduction            : 0.06
% 2.53/1.42  Demodulation         : 0.03
% 2.53/1.42  BG Simplification    : 0.02
% 2.53/1.42  Subsumption          : 0.03
% 2.53/1.42  Abstraction          : 0.01
% 2.53/1.42  MUC search           : 0.00
% 2.53/1.42  Cooper               : 0.00
% 2.53/1.42  Total                : 0.60
% 2.53/1.42  Index Insertion      : 0.00
% 2.53/1.42  Index Deletion       : 0.00
% 2.53/1.42  Index Matching       : 0.00
% 2.53/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
