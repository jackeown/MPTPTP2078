%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:54 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 725 expanded)
%              Number of leaves         :   37 ( 304 expanded)
%              Depth                    :   31
%              Number of atoms          :  392 (3990 expanded)
%              Number of equality atoms :   42 ( 543 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_145,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_174,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_28,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_40,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_38,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_34,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_32,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_85,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m2_orders_2(C_128,A_129,B_130)
      | ~ m1_orders_1(B_130,k1_orders_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_87,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_90,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_34,c_87])).

tff(c_91,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_90])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_6,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [A_132,B_133,C_134] :
      ( m1_subset_1(k3_orders_2(A_132,B_133,C_134),k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(C_134,u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [A_148,A_149,B_150,C_151] :
      ( m1_subset_1(A_148,u1_struct_0(A_149))
      | ~ r2_hidden(A_148,k3_orders_2(A_149,B_150,C_151))
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_152,plain,(
    ! [A_149,B_150,C_151] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_149,B_150,C_151)),u1_struct_0(A_149))
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149)
      | k3_orders_2(A_149,B_150,C_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_159,plain,(
    ! [B_154,D_155,A_156,C_157] :
      ( r2_hidden(B_154,D_155)
      | ~ r2_hidden(B_154,k3_orders_2(A_156,D_155,C_157))
      | ~ m1_subset_1(D_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(C_157,u1_struct_0(A_156))
      | ~ m1_subset_1(B_154,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v5_orders_2(A_156)
      | ~ v4_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_232,plain,(
    ! [A_177,D_178,C_179] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_177,D_178,C_179)),D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_subset_1(C_179,u1_struct_0(A_177))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_177,D_178,C_179)),u1_struct_0(A_177))
      | ~ l1_orders_2(A_177)
      | ~ v5_orders_2(A_177)
      | ~ v4_orders_2(A_177)
      | ~ v3_orders_2(A_177)
      | v2_struct_0(A_177)
      | k3_orders_2(A_177,D_178,C_179) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_244,plain,(
    ! [A_182,B_183,C_184] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_182,B_183,C_184)),B_183)
      | ~ m1_subset_1(C_184,u1_struct_0(A_182))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_orders_2(A_182)
      | ~ v5_orders_2(A_182)
      | ~ v4_orders_2(A_182)
      | ~ v3_orders_2(A_182)
      | v2_struct_0(A_182)
      | k3_orders_2(A_182,B_183,C_184) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_152,c_232])).

tff(c_94,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_237,plain,(
    ! [D_178,C_179] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_178,C_179)),D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_178,C_179) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_178,C_179)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_94,c_232])).

tff(c_241,plain,(
    ! [D_178,C_179] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_178,C_179)),D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_178,C_179) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_178,C_179)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_237])).

tff(c_242,plain,(
    ! [D_178,C_179] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_178,C_179)),D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_178,C_179) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_178,C_179)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_241])).

tff(c_247,plain,(
    ! [C_184] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_184)),'#skF_5')
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_184) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_244,c_242])).

tff(c_275,plain,(
    ! [C_184] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_184)),'#skF_5')
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_184) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_91,c_247])).

tff(c_276,plain,(
    ! [C_184] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_184)),'#skF_5')
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_184) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_275])).

tff(c_30,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_295,plain,(
    ! [C_189] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_189)),'#skF_5')
      | ~ m1_subset_1(C_189,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_189) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_275])).

tff(c_26,plain,(
    ! [A_58,D_86,B_74,E_88] :
      ( r3_orders_2(A_58,k1_funct_1(D_86,u1_struct_0(A_58)),B_74)
      | ~ r2_hidden(B_74,E_88)
      | ~ m2_orders_2(E_88,A_58,D_86)
      | ~ m1_orders_1(D_86,k1_orders_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(k1_funct_1(D_86,u1_struct_0(A_58)),u1_struct_0(A_58))
      | ~ m1_subset_1(B_74,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | ~ v5_orders_2(A_58)
      | ~ v4_orders_2(A_58)
      | ~ v3_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_321,plain,(
    ! [A_195,D_196,C_197] :
      ( r3_orders_2(A_195,k1_funct_1(D_196,u1_struct_0(A_195)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)))
      | ~ m2_orders_2('#skF_5',A_195,D_196)
      | ~ m1_orders_1(D_196,k1_orders_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(k1_funct_1(D_196,u1_struct_0(A_195)),u1_struct_0(A_195))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)),u1_struct_0(A_195))
      | ~ l1_orders_2(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v4_orders_2(A_195)
      | ~ v3_orders_2(A_195)
      | v2_struct_0(A_195)
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_197) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_295,c_26])).

tff(c_326,plain,(
    ! [C_197] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_197) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_321])).

tff(c_329,plain,(
    ! [C_197] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_197) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_30,c_34,c_32,c_326])).

tff(c_331,plain,(
    ! [C_198] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_198)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_198)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_198) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_329])).

tff(c_335,plain,(
    ! [C_151] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_151)))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_152,c_331])).

tff(c_341,plain,(
    ! [C_151] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_151)))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_151) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_91,c_335])).

tff(c_344,plain,(
    ! [C_199] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)))
      | ~ m1_subset_1(C_199,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_199) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_341])).

tff(c_16,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_orders_2(A_33,B_34,C_35)
      | ~ r3_orders_2(A_33,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_33))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_346,plain,(
    ! [C_199] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_199,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_199) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_344,c_16])).

tff(c_349,plain,(
    ! [C_199] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_199,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_199) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_346])).

tff(c_351,plain,(
    ! [C_200] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_200,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_200) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_349])).

tff(c_355,plain,(
    ! [C_151] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_151)))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_152,c_351])).

tff(c_361,plain,(
    ! [C_151] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_151)))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_151) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_91,c_355])).

tff(c_362,plain,(
    ! [C_151] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_151)))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_151) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_361])).

tff(c_164,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( r2_orders_2(A_158,B_159,C_160)
      | ~ r2_hidden(B_159,k3_orders_2(A_158,D_161,C_160))
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ m1_subset_1(B_159,u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v4_orders_2(A_158)
      | ~ v3_orders_2(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_304,plain,(
    ! [A_190,D_191,C_192] :
      ( r2_orders_2(A_190,'#skF_1'(k3_orders_2(A_190,D_191,C_192)),C_192)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ m1_subset_1(C_192,u1_struct_0(A_190))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_190,D_191,C_192)),u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | ~ v5_orders_2(A_190)
      | ~ v4_orders_2(A_190)
      | ~ v3_orders_2(A_190)
      | v2_struct_0(A_190)
      | k3_orders_2(A_190,D_191,C_192) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_309,plain,(
    ! [D_191,C_192] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_191,C_192)),C_192)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_191,C_192) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_191,C_192)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_94,c_304])).

tff(c_313,plain,(
    ! [D_191,C_192] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_191,C_192)),C_192)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_191,C_192) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_191,C_192)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_309])).

tff(c_315,plain,(
    ! [D_193,C_194] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_193,C_194)),C_194)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_193,C_194) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_193,C_194)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_313])).

tff(c_18,plain,(
    ! [A_36,C_42,B_40] :
      ( ~ r2_orders_2(A_36,C_42,B_40)
      | ~ r1_orders_2(A_36,B_40,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ m1_subset_1(B_40,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36)
      | ~ v5_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_317,plain,(
    ! [C_194,D_193] :
      ( ~ r1_orders_2('#skF_2',C_194,'#skF_1'(k3_orders_2('#skF_2',D_193,C_194)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_193,C_194)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ m1_subset_1(D_193,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_193,C_194) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_193,C_194)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_315,c_18])).

tff(c_420,plain,(
    ! [C_214,D_215] :
      ( ~ r1_orders_2('#skF_2',C_214,'#skF_1'(k3_orders_2('#skF_2',D_215,C_214)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_215,C_214)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_215,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_214,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_215,C_214) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_215,C_214)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_317])).

tff(c_426,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_362,c_420])).

tff(c_432,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_91,c_426])).

tff(c_433,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_432])).

tff(c_447,plain,(
    ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_450,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_276,c_447])).

tff(c_456,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_450])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_456])).

tff(c_459,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_485,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_152,c_459])).

tff(c_491,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_91,c_36,c_485])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_46,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.52  
% 3.35/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.53  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.50/1.53  
% 3.50/1.53  %Foreground sorts:
% 3.50/1.53  
% 3.50/1.53  
% 3.50/1.53  %Background operators:
% 3.50/1.53  
% 3.50/1.53  
% 3.50/1.53  %Foreground operators:
% 3.50/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.50/1.53  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.50/1.53  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.50/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.50/1.53  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.50/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.53  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.50/1.53  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.50/1.53  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.50/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.50/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.53  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.50/1.53  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.50/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.50/1.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.50/1.53  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.50/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.53  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.50/1.53  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.50/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.50/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.53  
% 3.52/1.56  tff(f_199, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 3.52/1.56  tff(f_89, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.52/1.56  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.52/1.56  tff(f_69, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.52/1.56  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.52/1.56  tff(f_145, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.52/1.56  tff(f_174, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 3.52/1.56  tff(f_104, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.52/1.56  tff(f_119, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 3.52/1.56  tff(c_28, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_44, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_42, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_40, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_38, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_34, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_32, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_85, plain, (![C_128, A_129, B_130]: (m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~m2_orders_2(C_128, A_129, B_130) | ~m1_orders_1(B_130, k1_orders_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.52/1.56  tff(c_87, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_85])).
% 3.52/1.56  tff(c_90, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_34, c_87])).
% 3.52/1.56  tff(c_91, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_90])).
% 3.52/1.56  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_6, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.52/1.56  tff(c_106, plain, (![A_132, B_133, C_134]: (m1_subset_1(k3_orders_2(A_132, B_133, C_134), k1_zfmisc_1(u1_struct_0(A_132))) | ~m1_subset_1(C_134, u1_struct_0(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.52/1.56  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.56  tff(c_148, plain, (![A_148, A_149, B_150, C_151]: (m1_subset_1(A_148, u1_struct_0(A_149)) | ~r2_hidden(A_148, k3_orders_2(A_149, B_150, C_151)) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(resolution, [status(thm)], [c_106, c_2])).
% 3.52/1.56  tff(c_152, plain, (![A_149, B_150, C_151]: (m1_subset_1('#skF_1'(k3_orders_2(A_149, B_150, C_151)), u1_struct_0(A_149)) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149) | k3_orders_2(A_149, B_150, C_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_148])).
% 3.52/1.56  tff(c_159, plain, (![B_154, D_155, A_156, C_157]: (r2_hidden(B_154, D_155) | ~r2_hidden(B_154, k3_orders_2(A_156, D_155, C_157)) | ~m1_subset_1(D_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(C_157, u1_struct_0(A_156)) | ~m1_subset_1(B_154, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v5_orders_2(A_156) | ~v4_orders_2(A_156) | ~v3_orders_2(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.52/1.56  tff(c_232, plain, (![A_177, D_178, C_179]: (r2_hidden('#skF_1'(k3_orders_2(A_177, D_178, C_179)), D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_subset_1(C_179, u1_struct_0(A_177)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_177, D_178, C_179)), u1_struct_0(A_177)) | ~l1_orders_2(A_177) | ~v5_orders_2(A_177) | ~v4_orders_2(A_177) | ~v3_orders_2(A_177) | v2_struct_0(A_177) | k3_orders_2(A_177, D_178, C_179)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_159])).
% 3.52/1.56  tff(c_244, plain, (![A_182, B_183, C_184]: (r2_hidden('#skF_1'(k3_orders_2(A_182, B_183, C_184)), B_183) | ~m1_subset_1(C_184, u1_struct_0(A_182)) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_orders_2(A_182) | ~v5_orders_2(A_182) | ~v4_orders_2(A_182) | ~v3_orders_2(A_182) | v2_struct_0(A_182) | k3_orders_2(A_182, B_183, C_184)=k1_xboole_0)), inference(resolution, [status(thm)], [c_152, c_232])).
% 3.52/1.56  tff(c_94, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_91, c_2])).
% 3.52/1.56  tff(c_237, plain, (![D_178, C_179]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_178, C_179)), D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_179, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_178, C_179)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_178, C_179)), '#skF_5'))), inference(resolution, [status(thm)], [c_94, c_232])).
% 3.52/1.56  tff(c_241, plain, (![D_178, C_179]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_178, C_179)), D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_179, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_178, C_179)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_178, C_179)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_237])).
% 3.52/1.56  tff(c_242, plain, (![D_178, C_179]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_178, C_179)), D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_179, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_178, C_179)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_178, C_179)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_241])).
% 3.52/1.56  tff(c_247, plain, (![C_184]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_184)), '#skF_5') | ~m1_subset_1(C_184, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_184)=k1_xboole_0)), inference(resolution, [status(thm)], [c_244, c_242])).
% 3.52/1.56  tff(c_275, plain, (![C_184]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_184)), '#skF_5') | ~m1_subset_1(C_184, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_184)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_91, c_247])).
% 3.52/1.56  tff(c_276, plain, (![C_184]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_184)), '#skF_5') | ~m1_subset_1(C_184, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_184)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_275])).
% 3.52/1.56  tff(c_30, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.52/1.56  tff(c_295, plain, (![C_189]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_189)), '#skF_5') | ~m1_subset_1(C_189, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_189)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_275])).
% 3.52/1.56  tff(c_26, plain, (![A_58, D_86, B_74, E_88]: (r3_orders_2(A_58, k1_funct_1(D_86, u1_struct_0(A_58)), B_74) | ~r2_hidden(B_74, E_88) | ~m2_orders_2(E_88, A_58, D_86) | ~m1_orders_1(D_86, k1_orders_1(u1_struct_0(A_58))) | ~m1_subset_1(k1_funct_1(D_86, u1_struct_0(A_58)), u1_struct_0(A_58)) | ~m1_subset_1(B_74, u1_struct_0(A_58)) | ~l1_orders_2(A_58) | ~v5_orders_2(A_58) | ~v4_orders_2(A_58) | ~v3_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.52/1.56  tff(c_321, plain, (![A_195, D_196, C_197]: (r3_orders_2(A_195, k1_funct_1(D_196, u1_struct_0(A_195)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197))) | ~m2_orders_2('#skF_5', A_195, D_196) | ~m1_orders_1(D_196, k1_orders_1(u1_struct_0(A_195))) | ~m1_subset_1(k1_funct_1(D_196, u1_struct_0(A_195)), u1_struct_0(A_195)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197)), u1_struct_0(A_195)) | ~l1_orders_2(A_195) | ~v5_orders_2(A_195) | ~v4_orders_2(A_195) | ~v3_orders_2(A_195) | v2_struct_0(A_195) | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_197)=k1_xboole_0)), inference(resolution, [status(thm)], [c_295, c_26])).
% 3.52/1.56  tff(c_326, plain, (![C_197]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_197)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_321])).
% 3.52/1.56  tff(c_329, plain, (![C_197]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_197)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_30, c_34, c_32, c_326])).
% 3.52/1.56  tff(c_331, plain, (![C_198]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_198))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_198)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_198, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_198)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_329])).
% 3.52/1.56  tff(c_335, plain, (![C_151]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_151))) | ~m1_subset_1(C_151, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_152, c_331])).
% 3.52/1.56  tff(c_341, plain, (![C_151]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_151))) | ~m1_subset_1(C_151, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_151)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_91, c_335])).
% 3.52/1.56  tff(c_344, plain, (![C_199]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199))) | ~m1_subset_1(C_199, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_199)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_341])).
% 3.52/1.56  tff(c_16, plain, (![A_33, B_34, C_35]: (r1_orders_2(A_33, B_34, C_35) | ~r3_orders_2(A_33, B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_33)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.52/1.56  tff(c_346, plain, (![C_199]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_199, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_199)=k1_xboole_0)), inference(resolution, [status(thm)], [c_344, c_16])).
% 3.52/1.56  tff(c_349, plain, (![C_199]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_199, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_199)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_346])).
% 3.52/1.56  tff(c_351, plain, (![C_200]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_200, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_200)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_349])).
% 3.52/1.56  tff(c_355, plain, (![C_151]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_151))) | ~m1_subset_1(C_151, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_152, c_351])).
% 3.52/1.56  tff(c_361, plain, (![C_151]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_151))) | ~m1_subset_1(C_151, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_151)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_91, c_355])).
% 3.52/1.56  tff(c_362, plain, (![C_151]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_151))) | ~m1_subset_1(C_151, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_151)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_361])).
% 3.52/1.56  tff(c_164, plain, (![A_158, B_159, C_160, D_161]: (r2_orders_2(A_158, B_159, C_160) | ~r2_hidden(B_159, k3_orders_2(A_158, D_161, C_160)) | ~m1_subset_1(D_161, k1_zfmisc_1(u1_struct_0(A_158))) | ~m1_subset_1(C_160, u1_struct_0(A_158)) | ~m1_subset_1(B_159, u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~v5_orders_2(A_158) | ~v4_orders_2(A_158) | ~v3_orders_2(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.52/1.56  tff(c_304, plain, (![A_190, D_191, C_192]: (r2_orders_2(A_190, '#skF_1'(k3_orders_2(A_190, D_191, C_192)), C_192) | ~m1_subset_1(D_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~m1_subset_1(C_192, u1_struct_0(A_190)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_190, D_191, C_192)), u1_struct_0(A_190)) | ~l1_orders_2(A_190) | ~v5_orders_2(A_190) | ~v4_orders_2(A_190) | ~v3_orders_2(A_190) | v2_struct_0(A_190) | k3_orders_2(A_190, D_191, C_192)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_164])).
% 3.52/1.56  tff(c_309, plain, (![D_191, C_192]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_191, C_192)), C_192) | ~m1_subset_1(D_191, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_192, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_191, C_192)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_191, C_192)), '#skF_5'))), inference(resolution, [status(thm)], [c_94, c_304])).
% 3.52/1.56  tff(c_313, plain, (![D_191, C_192]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_191, C_192)), C_192) | ~m1_subset_1(D_191, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_192, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_191, C_192)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_191, C_192)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_309])).
% 3.52/1.56  tff(c_315, plain, (![D_193, C_194]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_193, C_194)), C_194) | ~m1_subset_1(D_193, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_194, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_193, C_194)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_193, C_194)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_313])).
% 3.52/1.56  tff(c_18, plain, (![A_36, C_42, B_40]: (~r2_orders_2(A_36, C_42, B_40) | ~r1_orders_2(A_36, B_40, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_36)) | ~m1_subset_1(B_40, u1_struct_0(A_36)) | ~l1_orders_2(A_36) | ~v5_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.52/1.56  tff(c_317, plain, (![C_194, D_193]: (~r1_orders_2('#skF_2', C_194, '#skF_1'(k3_orders_2('#skF_2', D_193, C_194))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_193, C_194)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~m1_subset_1(D_193, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_194, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_193, C_194)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_193, C_194)), '#skF_5'))), inference(resolution, [status(thm)], [c_315, c_18])).
% 3.52/1.56  tff(c_420, plain, (![C_214, D_215]: (~r1_orders_2('#skF_2', C_214, '#skF_1'(k3_orders_2('#skF_2', D_215, C_214))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_215, C_214)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_215, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_214, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_215, C_214)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_215, C_214)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_317])).
% 3.52/1.56  tff(c_426, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_362, c_420])).
% 3.52/1.56  tff(c_432, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_91, c_426])).
% 3.52/1.56  tff(c_433, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_432])).
% 3.52/1.56  tff(c_447, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(splitLeft, [status(thm)], [c_433])).
% 3.52/1.56  tff(c_450, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_276, c_447])).
% 3.52/1.56  tff(c_456, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_450])).
% 3.52/1.56  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_456])).
% 3.52/1.56  tff(c_459, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_433])).
% 3.52/1.56  tff(c_485, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_152, c_459])).
% 3.52/1.56  tff(c_491, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_91, c_36, c_485])).
% 3.52/1.56  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_46, c_491])).
% 3.52/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  Inference rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Ref     : 0
% 3.52/1.56  #Sup     : 82
% 3.52/1.56  #Fact    : 0
% 3.52/1.56  #Define  : 0
% 3.52/1.56  #Split   : 2
% 3.52/1.56  #Chain   : 0
% 3.52/1.56  #Close   : 0
% 3.52/1.56  
% 3.52/1.56  Ordering : KBO
% 3.52/1.56  
% 3.52/1.56  Simplification rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Subsume      : 12
% 3.52/1.56  #Demod        : 129
% 3.52/1.56  #Tautology    : 12
% 3.52/1.56  #SimpNegUnit  : 32
% 3.52/1.56  #BackRed      : 0
% 3.52/1.56  
% 3.52/1.56  #Partial instantiations: 0
% 3.52/1.56  #Strategies tried      : 1
% 3.52/1.56  
% 3.52/1.56  Timing (in seconds)
% 3.52/1.56  ----------------------
% 3.52/1.57  Preprocessing        : 0.35
% 3.52/1.57  Parsing              : 0.19
% 3.52/1.57  CNF conversion       : 0.03
% 3.52/1.57  Main loop            : 0.42
% 3.52/1.57  Inferencing          : 0.17
% 3.52/1.57  Reduction            : 0.11
% 3.52/1.57  Demodulation         : 0.08
% 3.52/1.57  BG Simplification    : 0.02
% 3.52/1.57  Subsumption          : 0.08
% 3.52/1.57  Abstraction          : 0.02
% 3.52/1.57  MUC search           : 0.00
% 3.52/1.57  Cooper               : 0.00
% 3.52/1.57  Total                : 0.83
% 3.52/1.57  Index Insertion      : 0.00
% 3.52/1.57  Index Deletion       : 0.00
% 3.52/1.57  Index Matching       : 0.00
% 3.52/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
