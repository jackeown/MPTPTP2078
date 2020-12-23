%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:53 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 330 expanded)
%              Number of leaves         :   37 ( 149 expanded)
%              Depth                    :   30
%              Number of atoms          :  367 (1729 expanded)
%              Number of equality atoms :   37 ( 243 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_30,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_46,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_44,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_42,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_36,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_34,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_87,plain,(
    ! [C_131,A_132,B_133] :
      ( m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m2_orders_2(C_131,A_132,B_133)
      | ~ m1_orders_1(B_133,k1_orders_1(u1_struct_0(A_132)))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_89,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_87])).

tff(c_92,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_36,c_89])).

tff(c_93,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_92])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_4,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [A_134,B_135,C_136] :
      ( m1_subset_1(k3_orders_2(A_134,B_135,C_136),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(C_136,u1_struct_0(A_134))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [A_144,A_145,B_146,C_147] :
      ( m1_subset_1(A_144,u1_struct_0(A_145))
      | ~ r2_hidden(A_144,k3_orders_2(A_145,B_146,C_147))
      | ~ m1_subset_1(C_147,u1_struct_0(A_145))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_144,plain,(
    ! [A_145,B_146,C_147] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_145,B_146,C_147)),u1_struct_0(A_145))
      | ~ m1_subset_1(C_147,u1_struct_0(A_145))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145)
      | k3_orders_2(A_145,B_146,C_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_140])).

tff(c_32,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_145,plain,(
    ! [B_148,D_149,A_150,C_151] :
      ( r2_hidden(B_148,D_149)
      | ~ r2_hidden(B_148,k3_orders_2(A_150,D_149,C_151))
      | ~ m1_subset_1(D_149,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(C_151,u1_struct_0(A_150))
      | ~ m1_subset_1(B_148,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150)
      | ~ v5_orders_2(A_150)
      | ~ v4_orders_2(A_150)
      | ~ v3_orders_2(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_225,plain,(
    ! [A_180,D_181,C_182] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_180,D_181,C_182)),D_181)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(C_182,u1_struct_0(A_180))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_180,D_181,C_182)),u1_struct_0(A_180))
      | ~ l1_orders_2(A_180)
      | ~ v5_orders_2(A_180)
      | ~ v4_orders_2(A_180)
      | ~ v3_orders_2(A_180)
      | v2_struct_0(A_180)
      | k3_orders_2(A_180,D_181,C_182) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_237,plain,(
    ! [A_185,B_186,C_187] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_185,B_186,C_187)),B_186)
      | ~ m1_subset_1(C_187,u1_struct_0(A_185))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_orders_2(A_185)
      | ~ v5_orders_2(A_185)
      | ~ v4_orders_2(A_185)
      | ~ v3_orders_2(A_185)
      | v2_struct_0(A_185)
      | k3_orders_2(A_185,B_186,C_187) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_225])).

tff(c_100,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_230,plain,(
    ! [D_181,C_182] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),D_181)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_181,C_182) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_225])).

tff(c_234,plain,(
    ! [D_181,C_182] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),D_181)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_181,C_182) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_230])).

tff(c_235,plain,(
    ! [D_181,C_182] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),D_181)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_181,C_182) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_234])).

tff(c_240,plain,(
    ! [C_187] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_187)),'#skF_5')
      | ~ m1_subset_1(C_187,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_187) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_237,c_235])).

tff(c_256,plain,(
    ! [C_187] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_187)),'#skF_5')
      | ~ m1_subset_1(C_187,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_187) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_240])).

tff(c_273,plain,(
    ! [C_192] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_192)),'#skF_5')
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_192) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_256])).

tff(c_28,plain,(
    ! [A_54,D_82,B_70,E_84] :
      ( r3_orders_2(A_54,k1_funct_1(D_82,u1_struct_0(A_54)),B_70)
      | ~ r2_hidden(B_70,E_84)
      | ~ m2_orders_2(E_84,A_54,D_82)
      | ~ m1_orders_1(D_82,k1_orders_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(k1_funct_1(D_82,u1_struct_0(A_54)),u1_struct_0(A_54))
      | ~ m1_subset_1(B_70,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_921,plain,(
    ! [A_372,D_373,C_374] :
      ( r3_orders_2(A_372,k1_funct_1(D_373,u1_struct_0(A_372)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_374)))
      | ~ m2_orders_2('#skF_5',A_372,D_373)
      | ~ m1_orders_1(D_373,k1_orders_1(u1_struct_0(A_372)))
      | ~ m1_subset_1(k1_funct_1(D_373,u1_struct_0(A_372)),u1_struct_0(A_372))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_374)),u1_struct_0(A_372))
      | ~ l1_orders_2(A_372)
      | ~ v5_orders_2(A_372)
      | ~ v4_orders_2(A_372)
      | ~ v3_orders_2(A_372)
      | v2_struct_0(A_372)
      | ~ m1_subset_1(C_374,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_374) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_273,c_28])).

tff(c_926,plain,(
    ! [C_374] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_374)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_374)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_374,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_374) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_921])).

tff(c_929,plain,(
    ! [C_374] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_374)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_374)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_374,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_374) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_32,c_36,c_34,c_926])).

tff(c_931,plain,(
    ! [C_375] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_375)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_375)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_375,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_375) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_929])).

tff(c_935,plain,(
    ! [C_147] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_147)))
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_931])).

tff(c_941,plain,(
    ! [C_147] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_147)))
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_147) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_935])).

tff(c_944,plain,(
    ! [C_376] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_376)))
      | ~ m1_subset_1(C_376,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_376) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_941])).

tff(c_18,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_orders_2(A_29,B_30,C_31)
      | ~ r3_orders_2(A_29,B_30,C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_29))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29)
      | ~ v3_orders_2(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_946,plain,(
    ! [C_376] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_376)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_376)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_376,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_376) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_944,c_18])).

tff(c_949,plain,(
    ! [C_376] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_376)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_376)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_376,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_376) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_946])).

tff(c_951,plain,(
    ! [C_377] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_377)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_377)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_377,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_377) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_949])).

tff(c_955,plain,(
    ! [C_147] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_147)))
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_951])).

tff(c_961,plain,(
    ! [C_147] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_147)))
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_147) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_955])).

tff(c_964,plain,(
    ! [C_378] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_378)))
      | ~ m1_subset_1(C_378,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_378) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_961])).

tff(c_169,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( r2_orders_2(A_155,B_156,C_157)
      | ~ r2_hidden(B_156,k3_orders_2(A_155,D_158,C_157))
      | ~ m1_subset_1(D_158,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_695,plain,(
    ! [A_327,D_328,C_329] :
      ( r2_orders_2(A_327,'#skF_1'(k3_orders_2(A_327,D_328,C_329)),C_329)
      | ~ m1_subset_1(D_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ m1_subset_1(C_329,u1_struct_0(A_327))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_327,D_328,C_329)),u1_struct_0(A_327))
      | ~ l1_orders_2(A_327)
      | ~ v5_orders_2(A_327)
      | ~ v4_orders_2(A_327)
      | ~ v3_orders_2(A_327)
      | v2_struct_0(A_327)
      | k3_orders_2(A_327,D_328,C_329) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_169])).

tff(c_712,plain,(
    ! [A_332,B_333,C_334] :
      ( r2_orders_2(A_332,'#skF_1'(k3_orders_2(A_332,B_333,C_334)),C_334)
      | ~ m1_subset_1(C_334,u1_struct_0(A_332))
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(A_332)))
      | ~ l1_orders_2(A_332)
      | ~ v5_orders_2(A_332)
      | ~ v4_orders_2(A_332)
      | ~ v3_orders_2(A_332)
      | v2_struct_0(A_332)
      | k3_orders_2(A_332,B_333,C_334) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_695])).

tff(c_20,plain,(
    ! [A_32,C_38,B_36] :
      ( ~ r2_orders_2(A_32,C_38,B_36)
      | ~ r1_orders_2(A_32,B_36,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ m1_subset_1(B_36,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32)
      | ~ v5_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_715,plain,(
    ! [A_332,C_334,B_333] :
      ( ~ r1_orders_2(A_332,C_334,'#skF_1'(k3_orders_2(A_332,B_333,C_334)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_332,B_333,C_334)),u1_struct_0(A_332))
      | ~ m1_subset_1(C_334,u1_struct_0(A_332))
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(A_332)))
      | ~ l1_orders_2(A_332)
      | ~ v5_orders_2(A_332)
      | ~ v4_orders_2(A_332)
      | ~ v3_orders_2(A_332)
      | v2_struct_0(A_332)
      | k3_orders_2(A_332,B_333,C_334) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_712,c_20])).

tff(c_967,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_964,c_715])).

tff(c_973,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46,c_44,c_42,c_40,c_93,c_967])).

tff(c_974,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_48,c_973])).

tff(c_981,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_974])).

tff(c_987,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_38,c_981])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_48,c_987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:15:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.78  
% 4.17/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.78  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.17/1.78  
% 4.17/1.78  %Foreground sorts:
% 4.17/1.78  
% 4.17/1.78  
% 4.17/1.78  %Background operators:
% 4.17/1.78  
% 4.17/1.78  
% 4.17/1.78  %Foreground operators:
% 4.17/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.17/1.78  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.17/1.78  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.17/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.17/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.17/1.78  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.17/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.17/1.78  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 4.17/1.78  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 4.17/1.78  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 4.17/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.17/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.78  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.17/1.78  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.17/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.17/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.17/1.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.17/1.78  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 4.17/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.17/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.78  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.17/1.78  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 4.17/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.17/1.78  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.17/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.17/1.78  
% 4.17/1.80  tff(f_194, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_orders_2)).
% 4.17/1.80  tff(f_84, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 4.17/1.80  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 4.17/1.80  tff(f_64, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 4.17/1.80  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.17/1.80  tff(f_140, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 4.17/1.80  tff(f_169, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_orders_2)).
% 4.17/1.80  tff(f_99, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 4.17/1.80  tff(f_114, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 4.17/1.80  tff(c_30, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_44, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_40, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_36, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_34, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_87, plain, (![C_131, A_132, B_133]: (m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~m2_orders_2(C_131, A_132, B_133) | ~m1_orders_1(B_133, k1_orders_1(u1_struct_0(A_132))) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.17/1.80  tff(c_89, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_87])).
% 4.17/1.80  tff(c_92, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_36, c_89])).
% 4.17/1.80  tff(c_93, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_92])).
% 4.17/1.80  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_4, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.17/1.80  tff(c_94, plain, (![A_134, B_135, C_136]: (m1_subset_1(k3_orders_2(A_134, B_135, C_136), k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(C_136, u1_struct_0(A_134)) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.17/1.80  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.17/1.80  tff(c_140, plain, (![A_144, A_145, B_146, C_147]: (m1_subset_1(A_144, u1_struct_0(A_145)) | ~r2_hidden(A_144, k3_orders_2(A_145, B_146, C_147)) | ~m1_subset_1(C_147, u1_struct_0(A_145)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145))), inference(resolution, [status(thm)], [c_94, c_2])).
% 4.17/1.80  tff(c_144, plain, (![A_145, B_146, C_147]: (m1_subset_1('#skF_1'(k3_orders_2(A_145, B_146, C_147)), u1_struct_0(A_145)) | ~m1_subset_1(C_147, u1_struct_0(A_145)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145) | k3_orders_2(A_145, B_146, C_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_140])).
% 4.17/1.80  tff(c_32, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.17/1.80  tff(c_145, plain, (![B_148, D_149, A_150, C_151]: (r2_hidden(B_148, D_149) | ~r2_hidden(B_148, k3_orders_2(A_150, D_149, C_151)) | ~m1_subset_1(D_149, k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(C_151, u1_struct_0(A_150)) | ~m1_subset_1(B_148, u1_struct_0(A_150)) | ~l1_orders_2(A_150) | ~v5_orders_2(A_150) | ~v4_orders_2(A_150) | ~v3_orders_2(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.17/1.80  tff(c_225, plain, (![A_180, D_181, C_182]: (r2_hidden('#skF_1'(k3_orders_2(A_180, D_181, C_182)), D_181) | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(C_182, u1_struct_0(A_180)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_180, D_181, C_182)), u1_struct_0(A_180)) | ~l1_orders_2(A_180) | ~v5_orders_2(A_180) | ~v4_orders_2(A_180) | ~v3_orders_2(A_180) | v2_struct_0(A_180) | k3_orders_2(A_180, D_181, C_182)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_145])).
% 4.17/1.80  tff(c_237, plain, (![A_185, B_186, C_187]: (r2_hidden('#skF_1'(k3_orders_2(A_185, B_186, C_187)), B_186) | ~m1_subset_1(C_187, u1_struct_0(A_185)) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_orders_2(A_185) | ~v5_orders_2(A_185) | ~v4_orders_2(A_185) | ~v3_orders_2(A_185) | v2_struct_0(A_185) | k3_orders_2(A_185, B_186, C_187)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_225])).
% 4.17/1.80  tff(c_100, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_93, c_2])).
% 4.17/1.80  tff(c_230, plain, (![D_181, C_182]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), D_181) | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_181, C_182)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_225])).
% 4.17/1.80  tff(c_234, plain, (![D_181, C_182]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), D_181) | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_181, C_182)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_230])).
% 4.17/1.80  tff(c_235, plain, (![D_181, C_182]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), D_181) | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_181, C_182)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_234])).
% 4.17/1.80  tff(c_240, plain, (![C_187]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_187)), '#skF_5') | ~m1_subset_1(C_187, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_187)=k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_235])).
% 4.17/1.80  tff(c_256, plain, (![C_187]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_187)), '#skF_5') | ~m1_subset_1(C_187, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_187)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_240])).
% 4.17/1.80  tff(c_273, plain, (![C_192]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_192)), '#skF_5') | ~m1_subset_1(C_192, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_192)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_256])).
% 4.17/1.80  tff(c_28, plain, (![A_54, D_82, B_70, E_84]: (r3_orders_2(A_54, k1_funct_1(D_82, u1_struct_0(A_54)), B_70) | ~r2_hidden(B_70, E_84) | ~m2_orders_2(E_84, A_54, D_82) | ~m1_orders_1(D_82, k1_orders_1(u1_struct_0(A_54))) | ~m1_subset_1(k1_funct_1(D_82, u1_struct_0(A_54)), u1_struct_0(A_54)) | ~m1_subset_1(B_70, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.17/1.80  tff(c_921, plain, (![A_372, D_373, C_374]: (r3_orders_2(A_372, k1_funct_1(D_373, u1_struct_0(A_372)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_374))) | ~m2_orders_2('#skF_5', A_372, D_373) | ~m1_orders_1(D_373, k1_orders_1(u1_struct_0(A_372))) | ~m1_subset_1(k1_funct_1(D_373, u1_struct_0(A_372)), u1_struct_0(A_372)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_374)), u1_struct_0(A_372)) | ~l1_orders_2(A_372) | ~v5_orders_2(A_372) | ~v4_orders_2(A_372) | ~v3_orders_2(A_372) | v2_struct_0(A_372) | ~m1_subset_1(C_374, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_374)=k1_xboole_0)), inference(resolution, [status(thm)], [c_273, c_28])).
% 4.17/1.80  tff(c_926, plain, (![C_374]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_374))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_374)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_374, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_374)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_921])).
% 4.17/1.80  tff(c_929, plain, (![C_374]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_374))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_374)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_374, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_374)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_32, c_36, c_34, c_926])).
% 4.17/1.80  tff(c_931, plain, (![C_375]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_375))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_375)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_375, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_375)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_929])).
% 4.17/1.80  tff(c_935, plain, (![C_147]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_147))) | ~m1_subset_1(C_147, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_931])).
% 4.17/1.80  tff(c_941, plain, (![C_147]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_147))) | ~m1_subset_1(C_147, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_147)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_935])).
% 4.17/1.80  tff(c_944, plain, (![C_376]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_376))) | ~m1_subset_1(C_376, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_376)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_941])).
% 4.17/1.80  tff(c_18, plain, (![A_29, B_30, C_31]: (r1_orders_2(A_29, B_30, C_31) | ~r3_orders_2(A_29, B_30, C_31) | ~m1_subset_1(C_31, u1_struct_0(A_29)) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_orders_2(A_29) | ~v3_orders_2(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.17/1.80  tff(c_946, plain, (![C_376]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_376))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_376)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_376, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_376)=k1_xboole_0)), inference(resolution, [status(thm)], [c_944, c_18])).
% 4.17/1.80  tff(c_949, plain, (![C_376]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_376))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_376)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_376, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_376)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_946])).
% 4.17/1.80  tff(c_951, plain, (![C_377]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_377))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_377)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_377, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_377)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_949])).
% 4.17/1.80  tff(c_955, plain, (![C_147]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_147))) | ~m1_subset_1(C_147, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_951])).
% 4.17/1.80  tff(c_961, plain, (![C_147]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_147))) | ~m1_subset_1(C_147, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_147)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_955])).
% 4.17/1.80  tff(c_964, plain, (![C_378]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_378))) | ~m1_subset_1(C_378, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_378)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_961])).
% 4.17/1.80  tff(c_169, plain, (![A_155, B_156, C_157, D_158]: (r2_orders_2(A_155, B_156, C_157) | ~r2_hidden(B_156, k3_orders_2(A_155, D_158, C_157)) | ~m1_subset_1(D_158, k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.17/1.80  tff(c_695, plain, (![A_327, D_328, C_329]: (r2_orders_2(A_327, '#skF_1'(k3_orders_2(A_327, D_328, C_329)), C_329) | ~m1_subset_1(D_328, k1_zfmisc_1(u1_struct_0(A_327))) | ~m1_subset_1(C_329, u1_struct_0(A_327)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_327, D_328, C_329)), u1_struct_0(A_327)) | ~l1_orders_2(A_327) | ~v5_orders_2(A_327) | ~v4_orders_2(A_327) | ~v3_orders_2(A_327) | v2_struct_0(A_327) | k3_orders_2(A_327, D_328, C_329)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_169])).
% 4.17/1.80  tff(c_712, plain, (![A_332, B_333, C_334]: (r2_orders_2(A_332, '#skF_1'(k3_orders_2(A_332, B_333, C_334)), C_334) | ~m1_subset_1(C_334, u1_struct_0(A_332)) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(A_332))) | ~l1_orders_2(A_332) | ~v5_orders_2(A_332) | ~v4_orders_2(A_332) | ~v3_orders_2(A_332) | v2_struct_0(A_332) | k3_orders_2(A_332, B_333, C_334)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_695])).
% 4.17/1.80  tff(c_20, plain, (![A_32, C_38, B_36]: (~r2_orders_2(A_32, C_38, B_36) | ~r1_orders_2(A_32, B_36, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~m1_subset_1(B_36, u1_struct_0(A_32)) | ~l1_orders_2(A_32) | ~v5_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.17/1.80  tff(c_715, plain, (![A_332, C_334, B_333]: (~r1_orders_2(A_332, C_334, '#skF_1'(k3_orders_2(A_332, B_333, C_334))) | ~m1_subset_1('#skF_1'(k3_orders_2(A_332, B_333, C_334)), u1_struct_0(A_332)) | ~m1_subset_1(C_334, u1_struct_0(A_332)) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(A_332))) | ~l1_orders_2(A_332) | ~v5_orders_2(A_332) | ~v4_orders_2(A_332) | ~v3_orders_2(A_332) | v2_struct_0(A_332) | k3_orders_2(A_332, B_333, C_334)=k1_xboole_0)), inference(resolution, [status(thm)], [c_712, c_20])).
% 4.17/1.80  tff(c_967, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_964, c_715])).
% 4.17/1.80  tff(c_973, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46, c_44, c_42, c_40, c_93, c_967])).
% 4.17/1.80  tff(c_974, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_48, c_973])).
% 4.17/1.80  tff(c_981, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_974])).
% 4.17/1.80  tff(c_987, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_38, c_981])).
% 4.17/1.80  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_48, c_987])).
% 4.17/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.80  
% 4.17/1.80  Inference rules
% 4.17/1.80  ----------------------
% 4.17/1.80  #Ref     : 0
% 4.17/1.80  #Sup     : 165
% 4.17/1.80  #Fact    : 0
% 4.17/1.80  #Define  : 0
% 4.17/1.80  #Split   : 2
% 4.17/1.80  #Chain   : 0
% 4.17/1.80  #Close   : 0
% 4.17/1.80  
% 4.17/1.81  Ordering : KBO
% 4.17/1.81  
% 4.17/1.81  Simplification rules
% 4.17/1.81  ----------------------
% 4.17/1.81  #Subsume      : 53
% 4.17/1.81  #Demod        : 318
% 4.17/1.81  #Tautology    : 22
% 4.17/1.81  #SimpNegUnit  : 69
% 4.17/1.81  #BackRed      : 14
% 4.17/1.81  
% 4.17/1.81  #Partial instantiations: 0
% 4.17/1.81  #Strategies tried      : 1
% 4.17/1.81  
% 4.17/1.81  Timing (in seconds)
% 4.17/1.81  ----------------------
% 4.41/1.81  Preprocessing        : 0.36
% 4.41/1.81  Parsing              : 0.20
% 4.41/1.81  CNF conversion       : 0.03
% 4.41/1.81  Main loop            : 0.61
% 4.41/1.81  Inferencing          : 0.25
% 4.41/1.81  Reduction            : 0.17
% 4.41/1.81  Demodulation         : 0.11
% 4.41/1.81  BG Simplification    : 0.03
% 4.41/1.81  Subsumption          : 0.12
% 4.41/1.81  Abstraction          : 0.03
% 4.41/1.81  MUC search           : 0.00
% 4.41/1.81  Cooper               : 0.00
% 4.41/1.81  Total                : 1.01
% 4.41/1.81  Index Insertion      : 0.00
% 4.41/1.81  Index Deletion       : 0.00
% 4.41/1.81  Index Matching       : 0.00
% 4.41/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
