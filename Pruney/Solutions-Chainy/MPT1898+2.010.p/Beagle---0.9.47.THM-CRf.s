%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:31 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 130 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 360 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_109,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    v3_tdlat_3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_24,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_147,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ v1_xboole_0(C_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(C_53))
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_153,plain,(
    ! [A_12,A_55] :
      ( ~ v1_xboole_0(A_12)
      | ~ r2_hidden(A_55,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_147])).

tff(c_154,plain,(
    ! [A_55] : ~ r2_hidden(A_55,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_1048,plain,(
    ! [A_136,B_137] :
      ( r2_hidden('#skF_4'(A_136,B_137),B_137)
      | v2_tex_2(B_137,A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v3_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1060,plain,(
    ! [A_136] :
      ( r2_hidden('#skF_4'(A_136,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v3_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_24,c_1048])).

tff(c_1066,plain,(
    ! [A_136] :
      ( v2_tex_2(k1_xboole_0,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v3_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_1060])).

tff(c_1921,plain,(
    ! [A_170,B_171] :
      ( m1_subset_1('#skF_5'(A_170,B_171),k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ v2_tex_2(B_171,A_170)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170)
      | ~ v3_tdlat_3(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    ! [B_34] :
      ( ~ v3_tex_2(B_34,'#skF_6')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1938,plain,(
    ! [B_171] :
      ( ~ v3_tex_2('#skF_5'('#skF_6',B_171),'#skF_6')
      | ~ v2_tex_2(B_171,'#skF_6')
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v3_tdlat_3('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1921,c_46])).

tff(c_1947,plain,(
    ! [B_171] :
      ( ~ v3_tex_2('#skF_5'('#skF_6',B_171),'#skF_6')
      | ~ v2_tex_2(B_171,'#skF_6')
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1938])).

tff(c_1949,plain,(
    ! [B_172] :
      ( ~ v3_tex_2('#skF_5'('#skF_6',B_172),'#skF_6')
      | ~ v2_tex_2(B_172,'#skF_6')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1947])).

tff(c_1987,plain,
    ( ~ v3_tex_2('#skF_5'('#skF_6',k1_xboole_0),'#skF_6')
    | ~ v2_tex_2(k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_1949])).

tff(c_1988,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1987])).

tff(c_1991,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v3_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1066,c_1988])).

tff(c_1994,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1991])).

tff(c_1996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1994])).

tff(c_1998,plain,(
    v2_tex_2(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1987])).

tff(c_786,plain,(
    ! [A_126,B_127] :
      ( v3_tex_2('#skF_5'(A_126,B_127),A_126)
      | ~ v2_tex_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ v3_tdlat_3(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_802,plain,(
    ! [A_126] :
      ( v3_tex_2('#skF_5'(A_126,k1_xboole_0),A_126)
      | ~ v2_tex_2(k1_xboole_0,A_126)
      | ~ l1_pre_topc(A_126)
      | ~ v3_tdlat_3(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_24,c_786])).

tff(c_1997,plain,(
    ~ v3_tex_2('#skF_5'('#skF_6',k1_xboole_0),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1987])).

tff(c_2002,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v3_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_802,c_1997])).

tff(c_2005,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1998,c_2002])).

tff(c_2007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2005])).

tff(c_2008,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2008,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.67  
% 3.95/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.68  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 3.95/1.68  
% 3.95/1.68  %Foreground sorts:
% 3.95/1.68  
% 3.95/1.68  
% 3.95/1.68  %Background operators:
% 3.95/1.68  
% 3.95/1.68  
% 3.95/1.68  %Foreground operators:
% 3.95/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.95/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.95/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.95/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.95/1.68  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.95/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.68  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.95/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.95/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.95/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.68  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.95/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.95/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.95/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.95/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.95/1.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.95/1.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.95/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.95/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.95/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.68  
% 4.31/1.70  tff(f_124, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 4.31/1.70  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.31/1.70  tff(f_65, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.31/1.70  tff(f_86, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tex_2)).
% 4.31/1.70  tff(f_109, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 4.31/1.70  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.31/1.70  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.31/1.70  tff(c_52, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.31/1.70  tff(c_50, plain, (v3_tdlat_3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.31/1.70  tff(c_48, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.31/1.70  tff(c_24, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.31/1.70  tff(c_147, plain, (![C_53, B_54, A_55]: (~v1_xboole_0(C_53) | ~m1_subset_1(B_54, k1_zfmisc_1(C_53)) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.31/1.70  tff(c_153, plain, (![A_12, A_55]: (~v1_xboole_0(A_12) | ~r2_hidden(A_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_147])).
% 4.31/1.70  tff(c_154, plain, (![A_55]: (~r2_hidden(A_55, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_153])).
% 4.31/1.70  tff(c_1048, plain, (![A_136, B_137]: (r2_hidden('#skF_4'(A_136, B_137), B_137) | v2_tex_2(B_137, A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v3_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.31/1.70  tff(c_1060, plain, (![A_136]: (r2_hidden('#skF_4'(A_136, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_136) | ~l1_pre_topc(A_136) | ~v3_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_24, c_1048])).
% 4.31/1.70  tff(c_1066, plain, (![A_136]: (v2_tex_2(k1_xboole_0, A_136) | ~l1_pre_topc(A_136) | ~v3_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(negUnitSimplification, [status(thm)], [c_154, c_1060])).
% 4.31/1.70  tff(c_1921, plain, (![A_170, B_171]: (m1_subset_1('#skF_5'(A_170, B_171), k1_zfmisc_1(u1_struct_0(A_170))) | ~v2_tex_2(B_171, A_170) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170) | ~v3_tdlat_3(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.31/1.70  tff(c_46, plain, (![B_34]: (~v3_tex_2(B_34, '#skF_6') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.31/1.70  tff(c_1938, plain, (![B_171]: (~v3_tex_2('#skF_5'('#skF_6', B_171), '#skF_6') | ~v2_tex_2(B_171, '#skF_6') | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v3_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1921, c_46])).
% 4.31/1.70  tff(c_1947, plain, (![B_171]: (~v3_tex_2('#skF_5'('#skF_6', B_171), '#skF_6') | ~v2_tex_2(B_171, '#skF_6') | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1938])).
% 4.31/1.70  tff(c_1949, plain, (![B_172]: (~v3_tex_2('#skF_5'('#skF_6', B_172), '#skF_6') | ~v2_tex_2(B_172, '#skF_6') | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1947])).
% 4.31/1.70  tff(c_1987, plain, (~v3_tex_2('#skF_5'('#skF_6', k1_xboole_0), '#skF_6') | ~v2_tex_2(k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_24, c_1949])).
% 4.31/1.70  tff(c_1988, plain, (~v2_tex_2(k1_xboole_0, '#skF_6')), inference(splitLeft, [status(thm)], [c_1987])).
% 4.31/1.70  tff(c_1991, plain, (~l1_pre_topc('#skF_6') | ~v3_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1066, c_1988])).
% 4.31/1.70  tff(c_1994, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1991])).
% 4.31/1.70  tff(c_1996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1994])).
% 4.31/1.70  tff(c_1998, plain, (v2_tex_2(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_1987])).
% 4.31/1.70  tff(c_786, plain, (![A_126, B_127]: (v3_tex_2('#skF_5'(A_126, B_127), A_126) | ~v2_tex_2(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126) | ~v3_tdlat_3(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.31/1.70  tff(c_802, plain, (![A_126]: (v3_tex_2('#skF_5'(A_126, k1_xboole_0), A_126) | ~v2_tex_2(k1_xboole_0, A_126) | ~l1_pre_topc(A_126) | ~v3_tdlat_3(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_24, c_786])).
% 4.31/1.70  tff(c_1997, plain, (~v3_tex_2('#skF_5'('#skF_6', k1_xboole_0), '#skF_6')), inference(splitRight, [status(thm)], [c_1987])).
% 4.31/1.70  tff(c_2002, plain, (~v2_tex_2(k1_xboole_0, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v3_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_802, c_1997])).
% 4.31/1.70  tff(c_2005, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1998, c_2002])).
% 4.31/1.70  tff(c_2007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2005])).
% 4.31/1.70  tff(c_2008, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitRight, [status(thm)], [c_153])).
% 4.31/1.70  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.31/1.70  tff(c_2011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2008, c_6])).
% 4.31/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.70  
% 4.31/1.70  Inference rules
% 4.31/1.70  ----------------------
% 4.31/1.70  #Ref     : 0
% 4.31/1.70  #Sup     : 405
% 4.31/1.70  #Fact    : 0
% 4.31/1.70  #Define  : 0
% 4.31/1.70  #Split   : 11
% 4.31/1.70  #Chain   : 0
% 4.31/1.70  #Close   : 0
% 4.31/1.70  
% 4.31/1.70  Ordering : KBO
% 4.31/1.70  
% 4.31/1.70  Simplification rules
% 4.31/1.70  ----------------------
% 4.31/1.70  #Subsume      : 57
% 4.31/1.70  #Demod        : 150
% 4.31/1.70  #Tautology    : 75
% 4.31/1.70  #SimpNegUnit  : 62
% 4.31/1.70  #BackRed      : 12
% 4.31/1.70  
% 4.31/1.70  #Partial instantiations: 0
% 4.31/1.70  #Strategies tried      : 1
% 4.31/1.70  
% 4.31/1.70  Timing (in seconds)
% 4.31/1.70  ----------------------
% 4.31/1.70  Preprocessing        : 0.31
% 4.31/1.70  Parsing              : 0.17
% 4.31/1.70  CNF conversion       : 0.02
% 4.31/1.70  Main loop            : 0.63
% 4.31/1.70  Inferencing          : 0.21
% 4.31/1.70  Reduction            : 0.18
% 4.31/1.70  Demodulation         : 0.11
% 4.31/1.70  BG Simplification    : 0.03
% 4.31/1.70  Subsumption          : 0.16
% 4.31/1.70  Abstraction          : 0.03
% 4.31/1.70  MUC search           : 0.00
% 4.31/1.70  Cooper               : 0.00
% 4.31/1.70  Total                : 0.99
% 4.31/1.70  Index Insertion      : 0.00
% 4.31/1.70  Index Deletion       : 0.00
% 4.31/1.70  Index Matching       : 0.00
% 4.31/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
